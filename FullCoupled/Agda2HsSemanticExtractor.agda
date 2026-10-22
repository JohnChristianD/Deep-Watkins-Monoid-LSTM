module FullCoupled.Agda2HsSemanticExtractor where

open import Haskell.Prelude
open import Haskell.Prim using
  ( eqNat; monusNat; AgdaString )

incrementExtractorNat : Nat → Nat
incrementExtractorNat n = n + 1

CharList : Type
CharList = List Char

-- Match the ASCII alphabet directly. The pinned Agda JavaScript backend in
-- this build does not emit the required character primitives for its builtin
-- Char module, so Ord Char and primIs* calls fail at runtime. Literal clauses
-- are ordinary source-level pattern matching and need no character primitive.
isAsciiAlpha : Char → Bool
isAsciiAlpha 'A' = True
isAsciiAlpha 'B' = True
isAsciiAlpha 'C' = True
isAsciiAlpha 'D' = True
isAsciiAlpha 'E' = True
isAsciiAlpha 'F' = True
isAsciiAlpha 'G' = True
isAsciiAlpha 'H' = True
isAsciiAlpha 'I' = True
isAsciiAlpha 'J' = True
isAsciiAlpha 'K' = True
isAsciiAlpha 'L' = True
isAsciiAlpha 'M' = True
isAsciiAlpha 'N' = True
isAsciiAlpha 'O' = True
isAsciiAlpha 'P' = True
isAsciiAlpha 'Q' = True
isAsciiAlpha 'R' = True
isAsciiAlpha 'S' = True
isAsciiAlpha 'T' = True
isAsciiAlpha 'U' = True
isAsciiAlpha 'V' = True
isAsciiAlpha 'W' = True
isAsciiAlpha 'X' = True
isAsciiAlpha 'Y' = True
isAsciiAlpha 'Z' = True
isAsciiAlpha 'a' = True
isAsciiAlpha 'b' = True
isAsciiAlpha 'c' = True
isAsciiAlpha 'd' = True
isAsciiAlpha 'e' = True
isAsciiAlpha 'f' = True
isAsciiAlpha 'g' = True
isAsciiAlpha 'h' = True
isAsciiAlpha 'i' = True
isAsciiAlpha 'j' = True
isAsciiAlpha 'k' = True
isAsciiAlpha 'l' = True
isAsciiAlpha 'm' = True
isAsciiAlpha 'n' = True
isAsciiAlpha 'o' = True
isAsciiAlpha 'p' = True
isAsciiAlpha 'q' = True
isAsciiAlpha 'r' = True
isAsciiAlpha 's' = True
isAsciiAlpha 't' = True
isAsciiAlpha 'u' = True
isAsciiAlpha 'v' = True
isAsciiAlpha 'w' = True
isAsciiAlpha 'x' = True
isAsciiAlpha 'y' = True
isAsciiAlpha 'z' = True
isAsciiAlpha _ = False

isAsciiDigit : Char → Bool
isAsciiDigit '0' = True
isAsciiDigit '1' = True
isAsciiDigit '2' = True
isAsciiDigit '3' = True
isAsciiDigit '4' = True
isAsciiDigit '5' = True
isAsciiDigit '6' = True
isAsciiDigit '7' = True
isAsciiDigit '8' = True
isAsciiDigit '9' = True
isAsciiDigit _ = False

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
isSourceSpace ' ' = True
isSourceSpace '\n' = True
isSourceSpace '\r' = True
isSourceSpace '\t' = True
isSourceSpace _ = False

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

isIdentifierChar : Char → Bool
isIdentifierChar '_' = True
isIdentifierChar '-' = True
isIdentifierChar c = isAsciiAlpha c || isAsciiDigit c

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

-- Only ASCII delimiters are searched by the source reader. Keep the
-- delimiter in the function's pattern so generated JavaScript does not need
-- the unavailable generic Char equality primitive from Haskell.Prim.Char.
containsColon : CharList → Bool
containsColon [] = False
containsColon (':' ∷ _) = True
containsColon (_ ∷ rest) = containsColon rest

containsEquals : CharList → Bool
containsEquals [] = False
containsEquals ('=' ∷ _) = True
containsEquals (_ ∷ rest) = containsEquals rest

lineContainsColon : String → Bool
lineContainsColon source = containsColon source

lineContainsEquals : String → Bool
lineContainsEquals source = containsEquals source

splitFirstColon : CharList → CharList × CharList
splitFirstColon [] = [] , []
splitFirstColon (':' ∷ rest) = [] , rest
splitFirstColon (c ∷ rest) =
  let (before , after) = splitFirstColon rest
  in c ∷ before , after

splitFirstEquals : CharList → CharList × CharList
splitFirstEquals [] = [] , []
splitFirstEquals ('=' ∷ rest) = [] , rest
splitFirstEquals (c ∷ rest) =
  let (before , after) = splitFirstEquals rest
  in c ∷ before , after

splitFirstColonString : String → String × String
splitFirstColonString source =
  let (before , after) = splitFirstColon source
  in before , after

splitFirstEqualsString : String → String × String
splitFirstEqualsString source =
  let (before , after) = splitFirstEquals source
  in before , after

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
              case lineContainsColon line of λ where
                False -> Nothing
                True ->
                  let (_ , fragment) = splitFirstColonString line
                  in Just (headerName , trimWhitespace fragment)

topLevelRecordHeaderType :
  String ->
  String ->
  Maybe (String × String)
topLevelRecordHeaderType name line =
  case lineContainsColon line of λ where
    False -> Nothing
    True ->
      case splitFirstColonString line of λ where
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
              case lineContainsEquals line of λ where
                False -> Nothing
                True ->
                  case splitFirstEqualsString line of λ where
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
          -- A record type is one independent graph root. Do not absorb its
          -- indented field declarations into the root's dependency signature;
          -- parseRecordFields scans those fields as separate nodes.
          scanLines
            sourceFile
            rest
            ScanIdle
            (MkSemanticDecl
              sourceFile
              name
              fragment
              ""
              SemanticTopLevel
              ""
              ∷ accumulator)
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

-- A record header is recorded as one independent graph node, not as a
-- dependency on every declaration in the body of that record.
recordHeaderIsolationRegression : Bool
recordHeaderIsolationRegression =
  case parseLines
    "Regression.agda"
    ( "record Example : Set where" ∷
      "  field" ∷
      "    fieldValue : Nat" ∷
      "ordinary : Example" ∷
      [] ) of λ where
    (declaration ∷ _) ->
      declName declaration == "Example" &&
      declSignature declaration == "Set where" &&
      declBody declaration == ""
    _ -> False

recordHeaderIsolationRegressionChecked :
  recordHeaderIsolationRegression ≡ True
recordHeaderIsolationRegressionChecked = refl

leadingSpaceCountChars :
  CharList ->
  Nat ->
  Nat
leadingSpaceCountChars [] count = count
leadingSpaceCountChars (c ∷ rest) count =
  if isSpace c then
    leadingSpaceCountChars rest (incrementExtractorNat count)
  else
    count

leadingSpaceCount :
  String ->
  Nat
leadingSpaceCount source =
  leadingSpaceCountChars
    source
    0

recordFieldHeader :
  String ->
  Maybe (String × String)
recordFieldHeader line =
  case firstWord line of λ where
    Nothing -> Nothing
    (Just candidate) ->
      case leadingSpaceCount line >= incrementExtractorNat (incrementExtractorNat (incrementExtractorNat (incrementExtractorNat 0))) of λ where
        False -> Nothing
        True ->
          case candidate == "field" || syntaxHead candidate of λ where
            True -> Nothing
            False ->
              case lineContainsColon line of λ where
                False -> Nothing
                True ->
                  case splitFirstColonString line of λ where
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

-- Make a record root depend on its separately represented projections/fields.
-- This gives graph search the semantic path Record -> Record.field -> type deps,
-- without reabsorbing the whole record body into the root's signature.
recordFieldNamesFor : String -> List SemanticDecl -> List String
recordFieldNamesFor container [] = []
recordFieldNamesFor container (candidate ∷ rest) =
  case declKind candidate of λ where
    SemanticTopLevel ->
      recordFieldNamesFor container rest
    SemanticRecordField ->
      if declContainer candidate == container then
        declName candidate ∷ recordFieldNamesFor container rest
      else
        recordFieldNamesFor container rest

attachRecordFieldNames :
  List SemanticDecl -> List SemanticDecl -> List SemanticDecl
attachRecordFieldNames fields [] = []
attachRecordFieldNames fields (decl ∷ rest) =
  case declKind decl of λ where
    SemanticRecordField ->
      decl ∷ attachRecordFieldNames fields rest
    SemanticTopLevel ->
      let ownFieldNames = recordFieldNamesFor (declName decl) fields
          body =
            case ownFieldNames of λ where
              [] -> declBody decl
              _ -> unwordsString ownFieldNames
          connected =
            MkSemanticDecl
              (sourceFile decl)
              (declName decl)
              (declSignature decl)
              body
              (declKind decl)
              (declContainer decl)
      in connected ∷ attachRecordFieldNames fields rest

recordFieldIsolationRegression : Bool
recordFieldIsolationRegression =
  case parseRecordFields
    "Regression.agda"
    ( "record Example : Set where" ∷
      "  field" ∷
      "    fieldValue : Nat" ∷
      "ordinary : Example" ∷
      [] ) of λ where
    (fieldDecl ∷ _) ->
      case declKind fieldDecl of λ where
        SemanticRecordField ->
          declName fieldDecl == "Example.fieldValue" &&
          declSignature fieldDecl == "Nat" &&
          declContainer fieldDecl == "Example"
        SemanticTopLevel -> False
    _ -> False

recordFieldIsolationRegressionChecked :
  recordFieldIsolationRegression ≡ True
recordFieldIsolationRegressionChecked = refl

charListLength : CharList -> Nat
charListLength [] = 0
charListLength (_ ∷ rest) = incrementExtractorNat (charListLength rest)

dropN : Nat -> CharList -> CharList
dropN _ [] = []
dropN n (c ∷ rest) =
  if eqNat n 0
  then c ∷ rest
  else dropN (monusNat n 1) rest

matchesPrefix :
  CharList ->
  CharList ->
  Bool
matchesPrefix [] _ = True
matchesPrefix (_ ∷ _) [] = False
matchesPrefix (needle ∷ needles) (candidate ∷ candidates) =
  if needle == candidate then
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

recordFieldGraphEdgeRegression : Bool
recordFieldGraphEdgeRegression =
  let fields =
        parseRecordFields
          "Regression.agda"
          ( "record Example : Set where" ∷
            "  field" ∷
            "    fieldValue : Nat" ∷
            [] )
      declarations =
        attachRecordFieldNames fields
          (parseLines "Regression.agda"
            ("record Example : Set where" ∷ []))
  in
  case declarations of λ where
    (root ∷ []) ->
      declBody root == "Example.fieldValue" &&
      containsIdentifier (dependencyText root) "Example.fieldValue"
    _ -> False

recordFieldGraphEdgeRegressionChecked :
  recordFieldGraphEdgeRegression ≡ True
recordFieldGraphEdgeRegressionChecked = refl

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
      connectedRoots = attachRecordFieldNames fieldDeclarations topLevelDeclarations
  pure (fieldDeclarations ++ connectedRoots)

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
countNonreflexive [] = 0
countNonreflexive (law ∷ laws) =
  (if isReflexive law then 0 else incrementExtractorNat 0)
  + countNonreflexive laws

countComposite : List SemanticLaw -> Nat
countComposite [] = 0
countComposite (law ∷ laws) =
  (if isComposite law then incrementExtractorNat 0 else 0)
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
{-# COMPILE AGDA2HS containsColon #-}
{-# COMPILE AGDA2HS containsEquals #-}
{-# COMPILE AGDA2HS lineContainsColon #-}
{-# COMPILE AGDA2HS lineContainsEquals #-}
{-# COMPILE AGDA2HS splitFirstColon #-}
{-# COMPILE AGDA2HS splitFirstEquals #-}
{-# COMPILE AGDA2HS splitFirstColonString #-}
{-# COMPILE AGDA2HS splitFirstEqualsString #-}
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
{-# COMPILE AGDA2HS recordHeaderIsolationRegression #-}
{-# COMPILE AGDA2HS leadingSpaceCountChars #-}
{-# COMPILE AGDA2HS leadingSpaceCount #-}
{-# COMPILE AGDA2HS recordFieldHeader #-}
{-# COMPILE AGDA2HS finalizeRecordFieldState #-}
{-# COMPILE AGDA2HS scanRecordFields #-}
{-# COMPILE AGDA2HS parseRecordFields #-}
{-# COMPILE AGDA2HS recordFieldNamesFor #-}
{-# COMPILE AGDA2HS attachRecordFieldNames #-}
{-# COMPILE AGDA2HS recordFieldGraphEdgeRegression #-}
{-# COMPILE AGDA2HS recordFieldIsolationRegression #-}
{-# COMPILE AGDA2HS charListLength #-}
{-# COMPILE AGDA2HS incrementExtractorNat #-}
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
{-# COMPILE AGDA2HS hasAtLeastTwoDependencies #-}
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

------------------------------------------------------------------------
-- Static Pages model.
--
-- These constants are compiled with Agda's native JavaScript backend at
-- build time. The browser receives generated HTML and CSS only; there is no
-- client-side query, filtering, selection, or rendering state.
------------------------------------------------------------------------

sitePageTitle : AgdaString
sitePageTitle = "The Monoid LSTM Project — Canonical Agda Monoliths"

sitePageOverview : AgdaString
sitePageOverview =
  "A source-first account of the coupled monoid LSTM learner and its theorem monolith. The declaration index is generated from those two files only."

sitePageLearnerLabel : AgdaString
sitePageLearnerLabel = "Canonical learner semantics"

sitePageTheoremLabel : AgdaString
sitePageTheoremLabel = "Theorem and proof monolith"

sitePageRUSSTrustBoundary : AgdaString
sitePageRUSSTrustBoundary =
  "This page inventories declared assumptions; it does not certify global RUSS consistency. Kernel acceptance is relative to imported assumptions, postulates, compiler primitives, rewrite rules, and the trusted checker."

sitePageConsistencyStatus : AgdaString
sitePageConsistencyStatus = "Global RUSS consistency: not certified"

sitePageIsStatic : Bool
sitePageIsStatic = True
