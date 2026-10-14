module FullCoupled.Agda2HsSemanticExtractor where

open import Haskell.Prelude


CharList : Type
CharList = List Char

charBetween : Char → Char → Char → Bool
charBetween lower upper value =
  if lower <= value then
    if value <= upper then True else False
  else
    False

isAsciiAlpha : Char → Bool
isAsciiAlpha c =
  charBetween 'A' 'Z' c || charBetween 'a' 'z' c

isAsciiDigit : Char → Bool
isAsciiDigit c = charBetween '0' '9' c

isAsciiAlphaRegression : Bool
isAsciiAlphaRegression =
  isAsciiAlpha 'A' && isAsciiAlpha 'z' && not (isAsciiAlpha '7')

isAsciiAlphaRegressionChecked :
  isAsciiAlphaRegression ≡ True
isAsciiAlphaRegressionChecked = refl

isAsciiDigitRegression : Bool
isAsciiDigitRegression =
  isAsciiDigit '0' && isAsciiDigit '9' && not (isAsciiDigit 'x')

isAsciiDigitRegressionChecked :
  isAsciiDigitRegression ≡ True
isAsciiDigitRegressionChecked = refl

isSourceSpace : Char → Bool
isSourceSpace c =
  if eqChar c ' ' then True
  else if eqChar c '\n' then True
  else if eqChar c '\r' then True
  else eqChar c '\t'

data SemanticKind : Type where
  SemanticTopLevel : SemanticKind
  SemanticRecordField : SemanticKind

record SemanticDecl : Type where
  no-eta-equality; pattern
  constructor MkSemanticDecl
  field
    sourceFile : String
    declName : String
    declSignature : String
    declBody : String
    declKind : SemanticKind
    declContainer : String

open SemanticDecl public

record SemanticLaw : Type where
  no-eta-equality; pattern
  constructor MkSemanticLaw
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
  ScanIdle : ScanState
  ScanSignatureState :
    String -> List String -> ScanState
  ScanBodyState :
    String -> List String -> List String -> ScanState

data RecordFieldScanState : Type where
  OutsideRecord : RecordFieldScanState
  RecordWaiting :
    String -> RecordFieldScanState
  RecordFields :
    String -> RecordFieldScanState
  FieldCollecting :
    String -> String -> List String -> RecordFieldScanState

isIdentifierChar : Char -> Bool
isIdentifierChar c =
  if isAsciiAlpha c then
    True
  else if isAsciiDigit c then
    True
  else if eqChar c '_' then
    True
  else
    eqChar c '-'

isSpace : Char -> Bool
isSpace = isSourceSpace

isSpaceRegression : Bool
isSpaceRegression =
  isSpace ' ' && isSpace '\n' && not (isSpace 'x')

isSpaceRegressionChecked : isSpaceRegression ≡ True
isSpaceRegressionChecked = refl

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
  if eqChar target c then
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
  if eqChar target c then
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

planContains : String -> List String -> Bool
planContains _ [] = False
planContains name (candidate ∷ rest) =
  if name == candidate then
    True
  else
    planContains name rest

planContainsRegression : Bool
planContainsRegression =
  planContains "module" ("module" ∷ "data" ∷ [])
    && not (planContains "unknown" ("module" ∷ "data" ∷ []))

planContainsRegressionChecked : planContainsRegression ≡ True
planContainsRegressionChecked = refl

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

topLevelHeader :
  String ->
  Maybe (String × String)
topLevelHeader line =
  case firstWord line of λ where
    Nothing -> Nothing
    (Just headerName) ->
      case topLevelLine line of λ where
        False -> Nothing
        True ->
          case syntaxHead headerName || headerName == "--" of λ where
            True -> Nothing
            False ->
              case lineContainsChar ':' line of λ where
                False -> Nothing
                True ->
                  let (_ , fragment) = splitFirstCharString ':' line
                  in Just (headerName , trimWhitespace fragment)

topLevelRecordHeaderType :
  String ->
  String ->
  Maybe (String × String)
topLevelRecordHeaderType name line =
  case lineContainsChar ':' line of λ where
    False -> Nothing
    True ->
      case splitFirstCharString ':' line of λ where
        (_ , fragment) -> Just (name , trimWhitespace fragment)

topLevelRecordHeaderName :
  String ->
  Maybe (String × String)
topLevelRecordHeaderName line =
  case secondWord line of λ where
    Nothing -> Nothing
    (Just recordName) -> topLevelRecordHeaderType recordName line

topLevelRecordHeaderAtTopLevel :
  String ->
  Maybe (String × String)
topLevelRecordHeaderAtTopLevel line =
  if topLevelLine line then
    topLevelRecordHeaderName line
  else
    Nothing

topLevelRecordHeader :
  String ->
  Maybe (String × String)
topLevelRecordHeader line =
  case firstWord line of λ where
    Nothing -> Nothing
    (Just firstName) ->
      case firstName == "record" of λ where
        True -> topLevelRecordHeaderAtTopLevel line
        False -> Nothing

topLevelRecordHeaderRegression : Bool
topLevelRecordHeaderRegression =
  case topLevelRecordHeader "record Example : Set where" of λ where
    Nothing -> False
    (Just (recordName , recordType)) ->
      recordName == "Example" && recordType == "Set where"

topLevelRecordHeaderRegressionChecked :
  topLevelRecordHeaderRegression ≡ True
topLevelRecordHeaderRegressionChecked = refl

nestedRecordHeaderRejectedRegression : Bool
nestedRecordHeaderRejectedRegression =
  case topLevelRecordHeader "  record Example : Set where" of λ where
    Nothing -> True
    _ -> False

nestedRecordHeaderRejectedRegressionChecked :
  nestedRecordHeaderRejectedRegression ≡ True
nestedRecordHeaderRejectedRegressionChecked = refl

topLevelDeclarationHeader :
  String ->
  Maybe String
topLevelDeclarationHeader line =
  case topLevelHeader line of λ where
    Nothing -> Nothing
    (Just (name , _)) -> Just name

bodyClause :
  String ->
  String ->
  Maybe String
bodyClause name line =
  case firstWord line of λ where
    Nothing -> Nothing
    (Just lineName) ->
      case topLevelLine line of λ where
        False -> Nothing
        True ->
          case lineName == name of λ where
            False -> Nothing
            True ->
              case lineContainsChar '=' line of λ where
                False -> Nothing
                True ->
                  case splitFirstCharString '=' line of λ where
                    (_ , rhs) -> Just (trimWhitespace rhs)

bodyClauseRegression : Bool
bodyClauseRegression =
  case bodyClause "sample" "sample = body" of λ where
    Nothing -> False
    (Just body) -> body == "body"

bodyClauseRegressionChecked :
  bodyClauseRegression ≡ True
bodyClauseRegressionChecked = refl

bodyClauseRejectsIndentedRegression : Bool
bodyClauseRejectsIndentedRegression =
  case bodyClause "sample" "  sample = body" of λ where
    Nothing -> True
    _ -> False

bodyClauseRejectsIndentedRegressionChecked :
  bodyClauseRejectsIndentedRegression ≡ True
bodyClauseRejectsIndentedRegressionChecked = refl

unwordsString : List String -> String
unwordsString [] = ""
unwordsString (word ∷ wordsRest) =
  case wordsRest of λ where
    [] -> word
    _ -> word ++ " " ++ unwordsString wordsRest

finalizeScanState :
  String ->
  ScanState ->
  List SemanticDecl ->
  List SemanticDecl
finalizeScanState _ ScanIdle accumulator =
  accumulator
finalizeScanState sourceFile
  (ScanSignatureState name signatureReversed)
  accumulator =
  MkSemanticDecl
    sourceFile
    name
    (unwordsString (reverse signatureReversed))
    ""
    SemanticTopLevel
    ""
  ∷ accumulator
finalizeScanState sourceFile
  (ScanBodyState name signatureReversed bodyReversed)
  accumulator =
  MkSemanticDecl
    sourceFile
    name
    (unwordsString (reverse signatureReversed))
    (unwordsString (reverse bodyReversed))
    SemanticTopLevel
    ""
  ∷ accumulator

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
    ScanIdle ->
      case topLevelRecordHeader line of λ where
        (Just (name , fragment)) ->
          scanLines
            sourceFile
            rest
            (ScanSignatureState name (fragment ∷ []))
            accumulator
        Nothing ->
          case topLevelHeader line of λ where
            (Just (name , fragment)) ->
              scanLines
                sourceFile
                rest
                (ScanSignatureState name (fragment ∷ []))
                accumulator
            Nothing ->
              scanLines sourceFile rest ScanIdle accumulator
    (ScanSignatureState name signatureReversed) ->
      case bodyClause name line of λ where
        (Just body) ->
          scanLines
            sourceFile
            rest
            (ScanBodyState name signatureReversed (body ∷ []))
            accumulator
        Nothing ->
          case topLevelDeclarationHeader line of λ where
            (Just nextName) ->
              if nextName == name then
                scanLines
                  sourceFile
                  rest
                  (ScanSignatureState
                    name
                    (trimWhitespace line ∷ signatureReversed))
                  accumulator
              else
                case topLevelHeader line of λ where
                  Nothing ->
                    scanLines
                      sourceFile
                      rest
                      ScanIdle
                      (finalizeScanState
                        sourceFile
                        (ScanSignatureState name signatureReversed)
                        accumulator)
                  (Just (nextName , fragment)) ->
                    scanLines
                      sourceFile
                      rest
                      (ScanSignatureState nextName (fragment ∷ []))
                      (finalizeScanState
                        sourceFile
                        (ScanSignatureState name signatureReversed)
                        accumulator)
            Nothing ->
              scanLines
                sourceFile
                rest
                (ScanSignatureState
                  name
                  (trimWhitespace line ∷ signatureReversed))
                accumulator
    (ScanBodyState name signatureReversed bodyReversed) ->
      case topLevelDeclarationHeader line of λ where
        (Just nextName) ->
          if nextName == name then
            scanLines
              sourceFile
              rest
              (ScanBodyState
                name
                signatureReversed
                (trimWhitespace line ∷ bodyReversed))
              accumulator
          else
            case topLevelHeader line of λ where
              Nothing ->
                scanLines
                  sourceFile
                  rest
                  ScanIdle
                  (finalizeScanState
                    sourceFile
                    (ScanBodyState name signatureReversed bodyReversed)
                    accumulator)
              (Just (nextName , fragment)) ->
                scanLines
                  sourceFile
                  rest
                  (ScanSignatureState nextName (fragment ∷ []))
                  (finalizeScanState
                    sourceFile
                    (ScanBodyState name signatureReversed bodyReversed)
                    accumulator)
        Nothing ->
          scanLines
            sourceFile
            rest
            (ScanBodyState
              name
              signatureReversed
              (trimWhitespace line ∷ bodyReversed))
            accumulator

parseLines :
  String ->
  List String ->
  List SemanticDecl
parseLines sourceFile sourceLines =
  reverse (scanLines sourceFile sourceLines ScanIdle [])

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

leadingSpaceCount :
  String ->
  Nat
leadingSpaceCount source =
  leadingSpaceCountChars
    source
    zero

recordFieldHeader :
  String ->
  Maybe (String × String)
recordFieldHeader line =
  case firstWord line of λ where
    Nothing -> Nothing
    (Just candidate) ->
      case leadingSpaceCount line >= suc (suc (suc (suc zero))) of λ where
        False -> Nothing
        True ->
          case candidate == "field" || syntaxHead candidate of λ where
            True -> Nothing
            False ->
              case lineContainsChar ':' line of λ where
                False -> Nothing
                True ->
                  case splitFirstCharString ':' line of λ where
                    (before , after) ->
                      Just (trimWhitespace before , trimWhitespace after)

finalizeRecordFieldState :
  String ->
  RecordFieldScanState ->
  List SemanticDecl ->
  List SemanticDecl
finalizeRecordFieldState _ OutsideRecord accumulator =
  accumulator
finalizeRecordFieldState _ (RecordWaiting _) accumulator =
  accumulator
finalizeRecordFieldState _ (RecordFields _) accumulator =
  accumulator
finalizeRecordFieldState sourceFile
  (FieldCollecting recordName fieldName signatureReversed)
  accumulator =
  MkSemanticDecl
    sourceFile
    (recordName ++ "." ++ fieldName)
    (unwordsString (reverse signatureReversed))
    ""
    SemanticRecordField
    recordName
  ∷ accumulator


scanRecordFields :
  String ->
  List String ->
  RecordFieldScanState ->
  List SemanticDecl ->
  List SemanticDecl
scanRecordFields sourceFile [] state accumulator =
  finalizeRecordFieldState sourceFile state accumulator
scanRecordFields sourceFile (line ∷ rest) state accumulator =
  case topLevelLine line of λ where
    True ->
      case topLevelRecordHeader line of λ where
        (Just (recordName , _)) ->
          scanRecordFields
            sourceFile
            rest
            (RecordWaiting recordName)
            (finalizeRecordFieldState sourceFile state accumulator)
        Nothing ->
          scanRecordFields
            sourceFile
            rest
            OutsideRecord
            (finalizeRecordFieldState sourceFile state accumulator)
    False ->
      case state of λ where
        OutsideRecord ->
          scanRecordFields
            sourceFile
            rest
            OutsideRecord
            accumulator
        (RecordWaiting recordName) ->
          case firstWord line of λ where
            Nothing ->
              scanRecordFields
                sourceFile
                rest
                (RecordWaiting recordName)
                accumulator
            (Just lineWord) ->
              case lineWord == "field" of λ where
                True ->
                  scanRecordFields
                    sourceFile
                    rest
                    (RecordFields recordName)
                    accumulator
                False ->
                  scanRecordFields
                    sourceFile
                    rest
                    (RecordWaiting recordName)
                    accumulator
        (RecordFields recordName) ->
          case recordFieldHeader line of λ where
            (Just (fieldName , fragment)) ->
              scanRecordFields
                sourceFile
                rest
                (FieldCollecting
                  recordName
                  fieldName
                  (fragment ∷ []))
                accumulator
            Nothing ->
              scanRecordFields
                sourceFile
                rest
                (RecordFields recordName)
                accumulator
        (FieldCollecting recordName fieldName signatureReversed) ->
          case recordFieldHeader line of λ where
            (Just (nextFieldName , fragment)) ->
              scanRecordFields
                sourceFile
                rest
                (FieldCollecting
                  recordName
                  nextFieldName
                  (fragment ∷ []))
                (finalizeRecordFieldState
                  sourceFile
                  (FieldCollecting
                    recordName
                    fieldName
                    signatureReversed)
                  accumulator)
            Nothing ->
              scanRecordFields
                sourceFile
                rest
                (FieldCollecting
                  recordName
                  fieldName
                  (trimWhitespace line ∷ signatureReversed))
                accumulator

parseRecordFields :
  String ->
  List String ->
  List SemanticDecl
parseRecordFields sourceFile sourceLines =
  reverse
    (scanRecordFields
      sourceFile
      sourceLines
      OutsideRecord
      [])

charListLength : CharList -> Nat
charListLength [] = zero
charListLength (_ ∷ rest) = suc (charListLength rest)

dropN : Nat -> CharList -> CharList
dropN 0 chars = chars
dropN (suc n) [] = []
dropN (suc n) (_ ∷ rest) = dropN n rest

matchesPrefix :
  CharList ->
  CharList ->
  Bool
matchesPrefix [] _ = True
matchesPrefix (_ ∷ _) [] = False
matchesPrefix (needle ∷ needles) (candidate ∷ candidates) =
  if eqChar needle candidate then
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
containsIdentifierFrom previous (c ∷ rest) needle =
  if matchesPrefix needle (c ∷ rest) then
    boundaryBefore previous &&
    boundaryAfter (dropN (charListLength needle) (c ∷ rest))
  else
    containsIdentifierFrom (Just c) rest needle

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
findDependencies originSource name text (candidate ∷ rest) accumulator =
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

hasAtLeastTwoDependencies : List String -> Bool
hasAtLeastTwoDependencies (_ ∷ _ ∷ _) = True
hasAtLeastTwoDependencies _ = False

hasAtLeastTwoDependenciesRegression : Bool
hasAtLeastTwoDependenciesRegression =
  hasAtLeastTwoDependencies ("first" ∷ "second" ∷ [])
    && not (hasAtLeastTwoDependencies ("first" ∷ []))

hasAtLeastTwoDependenciesRegressionChecked :
  hasAtLeastTwoDependenciesRegression ≡ True
hasAtLeastTwoDependenciesRegressionChecked = refl

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
        hasAtLeastTwoDependencies dependencies &&
        not reflexive
      law =
        MkSemanticLaw
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

filterNonEmpty : List String -> List String
filterNonEmpty [] = []
filterNonEmpty (line ∷ rest) =
  if trimWhitespace line == "" then
    filterNonEmpty rest
  else
    line ∷ filterNonEmpty rest


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
    SemanticRecordField -> True
    SemanticTopLevel -> False

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

semanticLawSignature : SemanticLaw -> String
semanticLawSignature = lawSignature

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
{-# COMPILE AGDA2HS semanticLawSignature #-}
{-# COMPILE AGDA2HS semanticLawDependencies #-}
{-# COMPILE AGDA2HS countNonreflexive #-}
{-# COMPILE AGDA2HS countComposite #-}


















{-# COMPILE AGDA2HS charBetween #-}
{-# COMPILE AGDA2HS isAsciiAlpha #-}
{-# COMPILE AGDA2HS isAsciiDigit #-}
{-# COMPILE AGDA2HS isSourceSpace #-}
{-# COMPILE AGDA2HS isSpace #-}
{-# COMPILE AGDA2HS isIdentifierChar #-}
{-# COMPILE AGDA2HS isAsciiAlphaRegression #-}
{-# COMPILE AGDA2HS isAsciiDigitRegression #-}
{-# COMPILE AGDA2HS isSpaceRegression #-}
-- Parser regression values remain ordinary Agda definitions with kernel-checked proofs.
-- Do not COMPILE the regressions as Haskell roots: doing so forces extraction
-- of their parser-only helper closure instead of inlining it into the reader.
{-# COMPILE AGDA2HS planContains #-}
{-# COMPILE AGDA2HS planContainsRegression #-}

-- Production readSemanticLaws dependency closure. Parser regression values stay
-- Agda-only (their Checked proofs are still kernel-checked) to avoid a second
-- extraction root that bypasses the reader's established helper boundary.
{-# COMPILE AGDA2HS CharList #-}
{-# COMPILE AGDA2HS ScanState #-}
{-# COMPILE AGDA2HS RecordFieldScanState #-}
{-# COMPILE AGDA2HS dropLeadingSpaces #-}
{-# COMPILE AGDA2HS dropTrailingSpaces #-}
{-# COMPILE AGDA2HS trimWhitespace #-}
{-# COMPILE AGDA2HS firstWord #-}
{-# COMPILE AGDA2HS secondWord #-}
{-# COMPILE AGDA2HS containsChar #-}
{-# COMPILE AGDA2HS lineContainsChar #-}
{-# COMPILE AGDA2HS splitFirstChar #-}
{-# COMPILE AGDA2HS splitFirstCharString #-}
{-# COMPILE AGDA2HS topLevelLine #-}
{-# COMPILE AGDA2HS syntaxHead #-}
{-# COMPILE AGDA2HS topLevelHeader #-}
{-# COMPILE AGDA2HS topLevelRecordHeaderType #-}
{-# COMPILE AGDA2HS topLevelRecordHeaderName #-}
{-# COMPILE AGDA2HS topLevelRecordHeaderAtTopLevel #-}
{-# COMPILE AGDA2HS topLevelRecordHeader #-}
{-# COMPILE AGDA2HS topLevelDeclarationHeader #-}
{-# COMPILE AGDA2HS bodyClause #-}
{-# COMPILE AGDA2HS unwordsString #-}
{-# COMPILE AGDA2HS finalizeScanState #-}
{-# COMPILE AGDA2HS scanLines #-}
{-# COMPILE AGDA2HS parseLines #-}
{-# COMPILE AGDA2HS leadingSpaceCountChars #-}
{-# COMPILE AGDA2HS leadingSpaceCount #-}
{-# COMPILE AGDA2HS recordFieldHeader #-}
{-# COMPILE AGDA2HS finalizeRecordFieldState #-}
{-# COMPILE AGDA2HS scanRecordFields #-}
{-# COMPILE AGDA2HS parseRecordFields #-}
{-# COMPILE AGDA2HS charListLength #-}
{-# COMPILE AGDA2HS dropN #-}
{-# COMPILE AGDA2HS matchesPrefix #-}
{-# COMPILE AGDA2HS boundaryBefore #-}
{-# COMPILE AGDA2HS boundaryAfter #-}
{-# COMPILE AGDA2HS containsIdentifierFrom #-}
{-# COMPILE AGDA2HS containsIdentifier #-}
{-# COMPILE AGDA2HS dependencyText #-}
{-# COMPILE AGDA2HS findDependencies #-}
{-# COMPILE AGDA2HS semanticSignature #-}
{-# COMPILE AGDA2HS semanticReflexive #-}
{-# COMPILE AGDA2HS semanticLawsFromDeclarations #-}
{-# COMPILE AGDA2HS readSourceDeclarations #-}
{-# COMPILE AGDA2HS readAllSources #-}
{-# COMPILE AGDA2HS filterNonEmpty #-}
{-# COMPILE AGDA2HS isReflexive #-}
{-# COMPILE AGDA2HS isComposite #-}
{-# COMPILE AGDA2HS isRecordField #-}
{-# COMPILE AGDA2HS normalizeSignature #-}
{-# COMPILE AGDA2HS normalizedSignature #-}
{-# COMPILE AGDA2HS semanticLawKind #-}
{-# COMPILE AGDA2HS semanticLawContainer #-}
