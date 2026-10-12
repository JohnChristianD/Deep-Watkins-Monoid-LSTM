{-# OPTIONS
  --erasure
  --no-projection-like
#-}

module FullCoupled.Agda2HsSemanticExtractor where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
open import Haskell.Prelude
-- END MIRTH-SYNC COMMON IMPORTS

-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

CharList : Type
CharList = List Char

charEq : Char → Char → Bool
charEq a b = eqNat (c2n a) (c2n b)

natBetween : Nat → Nat → Nat → Bool
natBetween lo hi n =
  if lo <= n then
    if n <= hi then True else False
  else
    False

isAsciiAlpha : Char → Bool
isAsciiAlpha c =
  natBetween 65 90 (c2n c) || natBetween 97 122 (c2n c)

isAsciiDigit : Char → Bool
isAsciiDigit c = natBetween 48 57 (c2n c)

isSourceSpace : Char → Bool
isSourceSpace c =
  if charEq c ' ' then True
  else if charEq c '\n' then True
  else if charEq c '\r' then True
  else charEq c '\t'

data SemanticKind : Type where
  semantic-top-level : SemanticKind
  semantic-record-field : SemanticKind

record SemanticDecl : Type where
  constructor semanticDecl
  field
    sourceFile : String
    declName : String
    declSignature : String
    declBody : String
    declKind : SemanticKind
    declContainer : String

open SemanticDecl public

record SemanticLaw : Type where
  constructor semanticLaw
  field
    lawSource : String
    lawName : String
    lawReflexive : Bool
    lawComposite : Bool
    lawSignature : String
    lawDependencies : List String
    lawKind : SemanticKind
    lawContainer : String

open SemanticLaw public

data ScanState : Type where
  idle : ScanState
  signature-state :
    String -> List String -> ScanState
  body-state :
    String -> List String -> List String -> ScanState

data RecordFieldScanState : Type where
  outside-record : RecordFieldScanState
  record-waiting :
    String -> RecordFieldScanState
  record-fields :
    String -> RecordFieldScanState
  field-collecting :
    String -> String -> List String -> RecordFieldScanState

charEq : Char -> Char -> Bool
charEq = primCharEquality

isIdentifierChar : Char -> Bool
isIdentifierChar c =
  if isAsciiAlpha c then
    True
  else if isAsciiDigit c then
    True
  else if charEq c '_' then
    True
  else
    charEq c '-'

isSpace : Char -> Bool
isSpace = primIsSpace

dropLeadingSpaces : CharList -> CharList
dropLeadingSpaces [] = []
dropLeadingSpaces (c ∷ rest) =
  if isSpace c then
    dropLeadingSpaces rest
  else
    c ∷ rest

dropTrailingSpaces : CharList -> CharList
dropTrailingSpaces chars =
  reverse (dropLeadingSpaces (reverse chars))

trimWhitespace : String -> String
trimWhitespace source =
  dropTrailingSpaces
    (dropLeadingSpaces source)

firstWord : String -> Maybe String
firstWord source =
  case words source of λ where
    [] -> Nothing
    (word ∷ _) -> Just word

secondWord : String -> Maybe String
secondWord source =
  case words source of λ where
    (_ ∷ word ∷ _) -> Just word
    _ -> Nothing

containsChar : Char -> CharList -> Bool
containsChar _ [] = False
containsChar target (c ∷ rest) =
  if charEq target c then
    True
  else
    containsChar target rest

lineContainsChar : Char -> String -> Bool
lineContainsChar target source =
  containsChar target source

splitFirstChar :
  Char ->
  CharList ->
  CharList × CharList
splitFirstChar target [] = [] , []
splitFirstChar target (c ∷ rest) =
  if charEq target c then
    [] , rest
  else
    let (before , after) = splitFirstChar target rest
    in c ∷ before , after

splitFirstCharString :
  Char ->
  String ->
  String × String
splitFirstCharString target source =
  let (before , after) =
        splitFirstChar target source
  in
  before ,
  after

topLevelLine : String -> Bool
topLevelLine [] = False
topLevelLine source =
  case source of λ where
    [] -> False
    (c ∷ _) -> not (isSpace c)

syntaxHead : String -> Bool
syntaxHead word =
  planContains word
    ( "module" ∷
      "open" ∷
      "import" ∷
      "data" ∷
      "record" ∷
      "field" ∷
      "constructor" ∷
      "private" ∷
      "mutual" ∷
      "variable" ∷
      "infix" ∷
      "infixl" ∷
      "infixr" ∷
      "postulate" ∷
      "instance" ∷
      "macro" ∷
      [] )

planContains : String -> List String -> Bool
planContains _ [] = False
planContains name (candidate ∷ rest) =
  if name == candidate then
    True
  else
    planContains name rest

topLevelHeader :
  String ->
  Maybe (String × String)
topLevelHeader line =
  case firstWord line of λ where
    Nothing -> Nothing
    Just name ->
      if topLevelLine line then
        if syntaxHead name || name == "--" then
          Nothing
        else
          if lineContainsChar ':' line then
            let (_ , fragment) = splitFirstCharString ':' line
            in Just (name , trimWhitespace fragment)
          else
            Nothing
      else
        Nothing

topLevelRecordHeader :
  String ->
  Maybe (String × String)
topLevelRecordHeader line =
  if topLevelLine line then
    case firstWord line of λ where
      Just "record" ->
        case secondWord line of λ where
          Nothing -> Nothing
          Just name ->
            if lineContainsChar ':' line then
              let (_ , fragment) = splitFirstCharString ':' line
              in Just (name , trimWhitespace fragment)
            else
              Nothing
      _ -> Nothing
  else
    Nothing

topLevelDeclarationHeader :
  String ->
  Maybe String
topLevelDeclarationHeader line =
  case topLevelHeader line of λ where
    Nothing -> Nothing
    Just (name , _) -> Just name

bodyClause :
  String ->
  String ->
  Maybe String
bodyClause name line =
  if topLevelLine line then
    case firstWord line of λ where
      Just lineName ->
        if lineName == name then
          if lineContainsChar '=' line then
            let (_ , rhs) = splitFirstCharString '=' line
            in Just (trimWhitespace rhs)
          else
            Nothing
        else
          Nothing
      Nothing -> Nothing
  else
    Nothing

parseLines :
  String ->
  List String ->
  List SemanticDecl
parseLines sourceFile sourceLines =
  reverse (scanLines sourceFile sourceLines idle [])

scanLines :
  String ->
  List String ->
  ScanState ->
  List SemanticDecl ->
  List SemanticDecl
scanLines sourceFile [] state accumulator =
  finalizeScanState sourceFile state accumulator
scanLines sourceFile (line ∷ rest) state accumulator =
  case state of λ where
    idle ->
      case topLevelRecordHeader line of λ where
        Just (name , fragment) ->
          scanLines
            sourceFile
            rest
            (signature-state name (fragment ∷ []))
            accumulator
        Nothing ->
          case topLevelHeader line of λ where
            Just (name , fragment) ->
              scanLines
                sourceFile
                rest
                (signature-state name (fragment ∷ []))
                accumulator
            Nothing ->
              scanLines sourceFile rest idle accumulator
    signature-state name signatureReversed ->
      case bodyClause name line of λ where
        Just body ->
          scanLines
            sourceFile
            rest
            (body-state name signatureReversed (body ∷ []))
            accumulator
        Nothing ->
          case topLevelDeclarationHeader line of λ where
            Just nextName ->
              if nextName == name then
                scanLines
                  sourceFile
                  rest
                  (signature-state
                    name
                    (trimWhitespace line ∷ signatureReversed))
                  accumulator
              else
                scanLines
                  sourceFile
                  (line ∷ rest)
                  idle
                  (finalizeScanState
                    sourceFile
                    (signature-state name signatureReversed)
                    accumulator)
            Nothing ->
              scanLines
                sourceFile
                rest
                (signature-state
                  name
                  (trimWhitespace line ∷ signatureReversed))
                accumulator
    body-state name signatureReversed bodyReversed ->
      case topLevelDeclarationHeader line of λ where
        Just nextName ->
          if nextName == name then
            scanLines
              sourceFile
              rest
              (body-state
                name
                signatureReversed
                (trimWhitespace line ∷ bodyReversed))
              accumulator
          else
            scanLines
              sourceFile
              (line ∷ rest)
              idle
              (finalizeScanState
                sourceFile
                (body-state name signatureReversed bodyReversed)
                accumulator)
        Nothing ->
          scanLines
            sourceFile
            rest
            (body-state
              name
              signatureReversed
              (trimWhitespace line ∷ bodyReversed))
            accumulator

finalizeScanState :
  String ->
  ScanState ->
  List SemanticDecl ->
  List SemanticDecl
finalizeScanState _ idle accumulator =
  accumulator
finalizeScanState sourceFile
  (signature-state name signatureReversed)
  accumulator =
  semanticDecl
    sourceFile
    name
    (unwordsString (reverse signatureReversed))
    ""
    semantic-top-level
    ""
  ∷ accumulator
finalizeScanState sourceFile
  (body-state name signatureReversed bodyReversed)
  accumulator =
  semanticDecl
    sourceFile
    name
    (unwordsString (reverse signatureReversed))
    (unwordsString (reverse bodyReversed))
    semantic-top-level
    ""
  ∷ accumulator

leadingSpaceCount :
  String ->
  Nat
leadingSpaceCount source =
  leadingSpaceCountChars
    source
    zero

leadingSpaceCountChars :
  CharList ->
  Nat ->
  Nat
leadingSpaceCountChars [] count = count
leadingSpaceCountChars (c ∷ rest) count =
  if isSpace c then
    leadingSpaceCountChars rest (suc count)
  else
    count

recordFieldHeader :
  String ->
  Maybe (String × String)
recordFieldHeader line =
  if leadingSpaceCount line >= suc (suc (suc (suc zero))) then
    case firstWord line of λ where
      Nothing -> Nothing
      Just candidate ->
        if candidate == "field" || syntaxHead candidate then
          Nothing
        else
          if lineContainsChar ':' line then
            let (before , after) = splitFirstCharString ':' line
                name = trimWhitespace before
            in Just (name , trimWhitespace after)
          else
            Nothing
  else
    Nothing

parseRecordFields :
  String ->
  List String ->
  List SemanticDecl
parseRecordFields sourceFile sourceLines =
  reverse
    (scanRecordFields
      sourceFile
      sourceLines
      outside-record
      [])

scanRecordFields :
  String ->
  List String ->
  RecordFieldScanState ->
  List SemanticDecl ->
  List SemanticDecl
scanRecordFields sourceFile [] state accumulator =
  finalizeRecordFieldState sourceFile state accumulator
scanRecordFields sourceFile (line ∷ rest) state accumulator =
  if topLevelLine line then
    case topLevelRecordHeader line of λ where
      Just (recordName , _) ->
        scanRecordFields
          sourceFile
          rest
          (record-waiting recordName)
          (finalizeRecordFieldState sourceFile state accumulator)
      Nothing ->
        scanRecordFields
          sourceFile
          rest
          outside-record
          (finalizeRecordFieldState sourceFile state accumulator)
  else
    case state of λ where
      outside-record ->
        scanRecordFields
          sourceFile
          rest
          outside-record
          accumulator
      record-waiting recordName ->
        case firstWord line of λ where
          Just "field" ->
            scanRecordFields
              sourceFile
              rest
              (record-fields recordName)
              accumulator
          _ ->
            scanRecordFields
              sourceFile
              rest
              (record-waiting recordName)
              accumulator
      record-fields recordName ->
        case recordFieldHeader line of λ where
          Just (fieldName , fragment) ->
            scanRecordFields
              sourceFile
              rest
              (field-collecting
                recordName
                fieldName
                (fragment ∷ []))
              accumulator
          Nothing ->
            scanRecordFields
              sourceFile
              rest
              (record-fields recordName)
              accumulator
      field-collecting recordName fieldName signatureReversed ->
        case recordFieldHeader line of λ where
          Just (nextFieldName , fragment) ->
            scanRecordFields
              sourceFile
              rest
              (field-collecting
                recordName
                nextFieldName
                (fragment ∷ []))
              (finalizeRecordFieldState
                sourceFile
                (field-collecting
                  recordName
                  fieldName
                  signatureReversed)
                accumulator)
          Nothing ->
            scanRecordFields
              sourceFile
              rest
              (field-collecting
                recordName
                fieldName
                (trimWhitespace line ∷ signatureReversed))
              accumulator

finalizeRecordFieldState :
  String ->
  RecordFieldScanState ->
  List SemanticDecl ->
  List SemanticDecl
finalizeRecordFieldState _ outside-record accumulator =
  accumulator
finalizeRecordFieldState _ (record-waiting _) accumulator =
  accumulator
finalizeRecordFieldState _ (record-fields _) accumulator =
  accumulator
finalizeRecordFieldState sourceFile
  (field-collecting recordName fieldName signatureReversed)
  accumulator =
  semanticDecl
    sourceFile
    (recordName ++ "." ++ fieldName)
    (unwordsString (reverse signatureReversed))
    ""
    semantic-record-field
    recordName
  ∷ accumulator

unwordsString : List String -> String
unwordsString [] = ""
unwordsString (word ∷ wordsRest) =
  case wordsRest of λ where
    [] -> word
    _ -> word ++ " " ++ unwordsString wordsRest

dropN : Nat -> CharList -> CharList
dropN zero chars = chars
dropN (suc n) [] = []
dropN (suc n) (_ ∷ rest) = dropN n rest

matchesPrefix :
  CharList ->
  CharList ->
  Bool
matchesPrefix [] _ = True
matchesPrefix (_ ∷ _) [] = False
matchesPrefix (needle ∷ needles) (candidate ∷ candidates) =
  if charEq needle candidate then
    matchesPrefix needles candidates
  else
    False

boundaryBefore :
  Maybe Char ->
  Bool
boundaryBefore Nothing = True
boundaryBefore (Just c) = not (isIdentifierChar c)

boundaryAfter : CharList -> Bool
boundaryAfter [] = True
boundaryAfter (c ∷ _) = not (isIdentifierChar c)

containsIdentifierFrom :
  Maybe Char ->
  CharList ->
  CharList ->
  Bool
containsIdentifierFrom _ [] _ = False
containsIdentifierFrom previous haystack needle =
  if matchesPrefix needle haystack then
    boundaryBefore previous &&
    boundaryAfter (dropN (length needle) haystack)
  else
    case haystack of λ where
      [] -> False
      (c ∷ rest) ->
        containsIdentifierFrom
          (Just c)
          rest
          needle

containsIdentifier :
  String ->
  String ->
  Bool
containsIdentifier text name =
  containsIdentifierFrom
    Nothing
    text
    name

dependencyText : SemanticDecl -> String
dependencyText decl =
  declSignature decl ++ " " ++ declBody decl

findDependencies :
  String ->
  String ->
  String ->
  List SemanticDecl ->
  List String ->
  List String
findDependencies _ _ _ [] accumulator =
  reverse accumulator
findDependencies originSource name text allDeclarations accumulator =
  case allDeclarations of λ where
    [] -> reverse accumulator
    (candidate ∷ rest) ->
      let targetSource = SemanticDecl.sourceFile candidate
          targetName = declName candidate
          targetId = targetSource ++ "#" ++ targetName
          alreadySeen = planContains targetId accumulator
          found =
            if targetName == name || alreadySeen then
              False
            else if targetSource == originSource then
              containsIdentifier text targetName
            else
              containsIdentifier text ("." ++ targetName)
          nextAccumulator =
            if found then
              targetId ∷ accumulator
            else
              accumulator
      in
      findDependencies
        originSource
        name
        text
        rest
        nextAccumulator

semanticSignature : SemanticDecl -> Bool
semanticSignature decl =
  declName decl /= "" &&
  declSignature decl /= ""

semanticReflexive : SemanticDecl -> Bool
semanticReflexive decl =
  trimWhitespace (declBody decl) == "refl"

semanticLawsFromDeclarations :
  List SemanticDecl ->
  List SemanticDecl ->
  List SemanticLaw
semanticLawsFromDeclarations _ [] = []
semanticLawsFromDeclarations allDeclarations (decl ∷ rest) =
  let dependencies =
        findDependencies
          (sourceFile decl)
          (declName decl)
          (dependencyText decl)
          allDeclarations
          []
      reflexive = semanticReflexive decl
      composite =
        (length dependencies >= suc (suc zero)) &&
        not reflexive
      law =
        semanticLaw
          (sourceFile decl)
          (declName decl)
          reflexive
          composite
          (declSignature decl)
          dependencies
          (declKind decl)
          (declContainer decl)
  in
  law ∷ semanticLawsFromDeclarations allDeclarations rest

readSourceDeclarations :
  String ->
  IO (List SemanticDecl)
readSourceDeclarations sourceFile = do
  source <- readFile sourceFile
  let sourceLines = lines source
      topLevelDeclarations = parseLines sourceFile sourceLines
      fieldDeclarations = parseRecordFields sourceFile sourceLines
  pure (fieldDeclarations ++ topLevelDeclarations)

readAllSources :
  List String ->
  List SemanticDecl ->
  IO (List SemanticDecl)
readAllSources [] accumulator =
  pure (reverse accumulator)
readAllSources (sourceFile ∷ rest) accumulator = do
  declarations <- readSourceDeclarations sourceFile
  readAllSources rest (reverse declarations ++ accumulator)

readSemanticLaws :
  String ->
  IO (List SemanticLaw)
readSemanticLaws manifest = do
  manifestText <- readFile manifest
  let files =
        filterNonEmpty (lines manifestText)
  declarations <- readAllSources files []
  let semanticDeclarations =
        filter semanticSignature declarations
  pure
    (semanticLawsFromDeclarations
      declarations
      semanticDeclarations)

filterNonEmpty : List String -> List String
filterNonEmpty [] = []
filterNonEmpty (line ∷ rest) =
  if trimWhitespace line == "" then
    filterNonEmpty rest
  else
    line ∷ filterNonEmpty rest

semanticLawId : SemanticLaw -> String
semanticLawId law =
  lawSource law ++ "#" ++ lawName law

isReflexive : SemanticLaw -> Bool
isReflexive law = lawReflexive law

isComposite : SemanticLaw -> Bool
isComposite law = lawComposite law

isRecordField : SemanticLaw -> Bool
isRecordField law =
  case lawKind law of λ where
    semantic-record-field -> True
    semantic-top-level -> False

normalizeSignature : String -> String
normalizeSignature signature =
  unwordsString (words signature)

normalizedSignature : SemanticLaw -> String
normalizedSignature law =
  normalizeSignature (lawSignature law)

countNonreflexive : List SemanticLaw -> Nat
countNonreflexive [] = zero
countNonreflexive (law ∷ laws) =
  (if isReflexive law then zero else suc zero)
  + countNonreflexive laws

countComposite : List SemanticLaw -> Nat
countComposite [] = zero
countComposite (law ∷ laws) =
  (if isComposite law then suc zero else zero)
  + countComposite laws

semanticLawName : SemanticLaw -> String
semanticLawName = lawName

semanticLawDependencies : SemanticLaw -> List String
semanticLawDependencies = lawDependencies

semanticLawKind : SemanticLaw -> SemanticKind
semanticLawKind = lawKind

semanticLawContainer : SemanticLaw -> String
semanticLawContainer = lawContainer

{-# COMPILE AGDA2HS SemanticKind #-}
{-# COMPILE AGDA2HS SemanticDecl #-}
{-# COMPILE AGDA2HS SemanticLaw #-}
{-# COMPILE AGDA2HS readSemanticLaws #-}
{-# COMPILE AGDA2HS semanticLawId #-}
{-# COMPILE AGDA2HS semanticLawName #-}
{-# COMPILE AGDA2HS semanticLawDependencies #-}
{-# COMPILE AGDA2HS countNonreflexive #-}
{-# COMPILE AGDA2HS countComposite #-}
