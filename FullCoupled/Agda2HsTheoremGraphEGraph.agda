module FullCoupled.Agda2HsTheoremGraphEGraph where

open import Haskell.Prelude
open import Haskell.Prim using (eqNat; monusNat)

incrementEGraphNat : Nat → Nat
incrementEGraphNat n = n + 1

data Expr : Type where
  ExprAtom : String -> Expr
  ExprApp : String -> List Expr -> Expr

data Pattern : Type where
  PatternVar : String -> Pattern
  PatternApp : String -> List Pattern -> Pattern

record RewriteRule : Type where
  no-eta-equality; pattern
  constructor MkRewriteRule
  field
    ruleName : String
    lhs : Pattern
    rhs : Pattern

open RewriteRule public

record ENode : Type where
  no-eta-equality; pattern
  constructor MkENode
  field
    symbol : String
    children : List Nat

open ENode public

record Binding : Type where
  no-eta-equality; pattern
  constructor MkBinding
  field
    node : ENode
    classId : Nat

open Binding public

bindingCount : List Binding -> Nat
bindingCount [] = 0
bindingCount (_ ∷ rest) = incrementEGraphNat (bindingCount rest)

natListCount : List Nat -> Nat
natListCount [] = 0
natListCount (_ ∷ rest) = incrementEGraphNat (natListCount rest)

bindingCountRegression : Bool
bindingCountRegression =
  bindingCount [] == 0
  && bindingCount (MkBinding (MkENode "ExprAtom" []) 0 ∷ []) == incrementEGraphNat 0

bindingCountRegressionChecked : bindingCountRegression ≡ True
bindingCountRegressionChecked = refl

record EGraph : Type where
  no-eta-equality; pattern
  constructor MkEGraph
  field
    nextId : Nat
    parents : List (Nat × Nat)
    bindings : List Binding

open EGraph public

record Substitution : Type where
  no-eta-equality; pattern
  constructor MkSubstitution
  field
    entries : List (String × Nat)

open Substitution public

record ClassAnalysis : Type where
  no-eta-equality; pattern
  constructor MkClassAnalysis
  field
    analysisClass : Nat
    analysisENodeCount : Nat
    analysisMinLocalCost : Nat

open ClassAnalysis public

classAnalysisCount : List ClassAnalysis -> Nat
classAnalysisCount [] = 0
classAnalysisCount (_ ∷ rest) = incrementEGraphNat (classAnalysisCount rest)

record SaturationReport : Type where
  no-eta-equality; pattern
  constructor MkSaturationReport
  field
    saturationIterations : Nat
    saturationRewrites : Nat
    saturationChanged : Bool
    saturationComplete : Bool

open SaturationReport public

record Extraction : Type where
  no-eta-equality; pattern
  constructor MkExtraction
  field
    extractedExpr : Expr
    extractedCost : Nat

open Extraction public

record ChildExtraction : Type where
  no-eta-equality; pattern
  constructor MkChildExtraction
  field
    extractedChildren : List Expr
    extractedCostSum : Nat

open ChildExtraction public

memberNat : Nat -> List Nat -> Bool
memberNat _ [] = False
memberNat x (y ∷ ys) =
  if x == y then True else memberNat x ys

natEqual : Nat -> Nat -> Bool
natEqual left right = eqNat left right

lookupNatPair : Nat -> List (Nat × Nat) -> Maybe Nat
lookupNatPair _ [] = Nothing
lookupNatPair key ((candidate , value) ∷ rest) =
  if natEqual key candidate then Just value else lookupNatPair key rest

lookupStringPair : String -> List (String × Nat) -> Maybe Nat
lookupStringPair _ [] = Nothing
lookupStringPair key ((candidate , value) ∷ rest) =
  if key == candidate then Just value else lookupStringPair key rest

lookupNatPairRegression : Bool
lookupNatPairRegression =
  case lookupNatPair 2 ((1 , 10) ∷ (2 , 20) ∷ []) of λ where
    Nothing -> False
    (Just value) -> value == 20

lookupNatPairRegressionChecked : lookupNatPairRegression ≡ True
lookupNatPairRegressionChecked = refl

lookupStringPairRegression : Bool
lookupStringPairRegression =
  case lookupStringPair "right" (("left" , 1) ∷ ("right" , 2) ∷ []) of λ where
    Nothing -> False
    (Just value) -> value == 2

lookupStringPairRegressionChecked : lookupStringPairRegression ≡ True
lookupStringPairRegressionChecked = refl

setPair : {a b : Type} -> a -> b -> List (a × b) -> List (a × b)
setPair key value pairs = (key , value) ∷ pairs

listEqualNat : List Nat -> List Nat -> Bool
listEqualNat [] [] = True
listEqualNat [] (_ ∷ _) = False
listEqualNat (_ ∷ _) [] = False
listEqualNat (x ∷ xs) (y ∷ ys) =
  if x == y then listEqualNat xs ys else False

parentsLookup : Nat -> List (Nat × Nat) -> Nat
parentsLookup key parents =
  case lookupNatPair key parents of λ where
    Nothing -> key
    (Just parent) -> parent

-- Lazy unit-token fuel avoids matching on Agda's built-in Nat in extracted
-- Haskell. Every parent chain has at most one node per stored binding.
unitFuel : List Binding -> List ⊤
unitFuel [] = []
unitFuel (_ ∷ rest) = tt ∷ unitFuel rest

-- Give union-find, rebuild, and saturation one more step than the number of
-- interned nodes. Haskell only demands this lazy spine as recursive calls run.
graphFuel : EGraph -> List ⊤
graphFuel graph = tt ∷ unitFuel (bindings graph)

-- Resolve parent links with an explicit finite bound; exhausted fuel returns
-- the current representative rather than recursing indefinitely on bad data.
rootWithFuel : List ⊤ -> Nat -> List (Nat × Nat) -> Nat
rootWithFuel [] id _ = id
rootWithFuel (_ ∷ fuel) id parents =
  let parent = parentsLookup id parents in
  if parent == id then id else rootWithFuel fuel parent parents

root : EGraph -> Nat -> Nat
root graph id = rootWithFuel (graphFuel graph) id (parents graph)

canonicalChildren : EGraph -> List Nat -> List Nat
canonicalChildren _ [] = []
canonicalChildren graph (x ∷ xs) =
  root graph x ∷ canonicalChildren graph xs

canonicalNode : EGraph -> ENode -> ENode
canonicalNode graph (MkENode symbol children) =
  MkENode symbol (canonicalChildren graph children)

sameENode : ENode -> ENode -> Bool
sameENode (MkENode sx xs) (MkENode sy ys) =
  if sx == sy then listEqualNat xs ys else False

findBindingByNode : EGraph -> ENode -> List Binding -> Maybe Nat
findBindingByNode _ _ [] = Nothing
findBindingByNode graph target (MkBinding candidate id ∷ rest) =
  if sameENode target (canonicalNode graph candidate) then Just (root graph id)
  else findBindingByNode graph target rest

freshClass : EGraph -> Nat × EGraph
freshClass graph =
  let id = nextId graph
      graph' = MkEGraph (incrementEGraphNat id) (setPair id id (parents graph)) (bindings graph)
  in id , graph'

hashconsNode : ENode -> EGraph -> Nat × EGraph
hashconsNode raw graph =
  let node = canonicalNode graph raw in
  case findBindingByNode graph node (bindings graph) of λ where
    Nothing ->
      let (id , graph') = freshClass graph in
      id ,
      MkEGraph
        (nextId graph')
        (parents graph')
        (MkBinding node id ∷ bindings graph')
    (Just id) -> root graph id , graph

mutual
  addExpr : Expr -> EGraph -> Nat × EGraph
  addExpr (ExprAtom symbol) graph =
    hashconsNode (MkENode symbol []) graph
  addExpr (ExprApp symbol children) graph =
    let (childIds , graph') = addExprs children graph in
    hashconsNode (MkENode symbol childIds) graph'

  addExprs : List Expr -> EGraph -> List Nat × EGraph
  addExprs [] graph = [] , graph
  addExprs (x ∷ xs) graph =
    let (id , graph') = addExpr x graph
        (ids , graph'') = addExprs xs graph'
    in id ∷ ids , graph''

mergeRoots : Nat -> Nat -> EGraph -> EGraph
mergeRoots left right graph =
  let l = root graph left
      r = root graph right
  in
  if l == r then graph else
    let small = if l < r then l else r
        large = if l < r then r else l
    in MkEGraph (nextId graph) (setPair large small (parents graph)) (bindings graph)

equivalent : Nat -> Nat -> EGraph -> Bool
equivalent left right graph = root graph left == root graph right

findOtherNode :
  ENode -> Nat -> EGraph -> List Binding -> Maybe Nat
findOtherNode _ _ _ [] = Nothing
findOtherNode target excluded graph (MkBinding candidate id ∷ rest) =
  if id == excluded then findOtherNode target excluded graph rest
  else if sameENode target (canonicalNode graph candidate) then Just id
  else findOtherNode target excluded graph rest

rebuildBindings :
  List Binding -> EGraph -> Bool -> EGraph × Bool
rebuildBindings [] graph changed = graph , changed
rebuildBindings (MkBinding node id ∷ rest) graph changed =
  let canonical = canonicalNode graph node
  in
  case findOtherNode canonical id graph (bindings graph) of λ where
    Nothing -> rebuildBindings rest graph changed
    (Just other) ->
      if equivalent id other graph then
        rebuildBindings rest graph changed
      else
        rebuildBindings rest (mergeRoots id other graph) True

canonicalizeBindings : List Binding -> EGraph -> List Binding
canonicalizeBindings [] _ = []
canonicalizeBindings (MkBinding node id ∷ rest) graph =
  MkBinding (canonicalNode graph node) id ∷ canonicalizeBindings rest graph

rebuildPass : EGraph -> EGraph × Bool
rebuildPass graph =
  let canonical = canonicalizeBindings (bindings graph) graph
      graph' = MkEGraph (nextId graph) (parents graph) canonical
  in rebuildBindings canonical graph' False

-- Rebuild until congruence stops merging classes or the graph-sized bound
-- is exhausted. Each successful pass strictly reduces the class partition.
rebuildWithFuel : List ⊤ -> EGraph -> EGraph
rebuildWithFuel [] graph = graph
rebuildWithFuel (_ ∷ fuel) graph =
  let (graph' , changed) = rebuildPass graph in
  if changed then rebuildWithFuel fuel graph' else graph'

rebuild : EGraph -> EGraph
rebuild graph = rebuildWithFuel (graphFuel graph) graph

merge : Nat -> Nat -> EGraph -> EGraph
merge left right graph = rebuild (mergeRoots left right graph)

lookupSubstitution : String -> Substitution -> Maybe Nat
lookupSubstitution name (MkSubstitution entries) = lookupStringPair name entries

bindSubstitution : String -> Nat -> Substitution -> Maybe Substitution
bindSubstitution name id (MkSubstitution entries) =
  case lookupSubstitution name (MkSubstitution entries) of λ where
    Nothing -> Just (MkSubstitution ((name , id) ∷ entries))
    (Just old) ->
      if old == id then Just (MkSubstitution entries) else Nothing

mutual
  matchPattern :
    Pattern -> Nat -> EGraph -> Substitution -> List Substitution
  matchPattern (PatternVar name) classId graph sub =
    case bindSubstitution name (root graph classId) sub of λ where
      Nothing -> []
      (Just result) -> result ∷ []
  matchPattern (PatternApp symbol patterns) classId graph sub =
    matchNodes symbol patterns (root graph classId) graph (bindings graph) sub

  matchNodes :
    String -> List Pattern -> Nat -> EGraph ->
    List Binding -> Substitution -> List Substitution
  matchNodes _ _ _ _ [] _ = []
  matchNodes symbol patterns target graph
    (MkBinding (MkENode candidate children) bindingId ∷ rest) sub =
    if root graph bindingId == target then
      if candidate == symbol then
        matchChildren patterns children graph sub
        ++ matchNodes symbol patterns target graph rest sub
      else matchNodes symbol patterns target graph rest sub
    else matchNodes symbol patterns target graph rest sub

  matchChildren :
    List Pattern -> List Nat -> EGraph ->
    Substitution -> List Substitution
  matchChildren [] [] _ sub = sub ∷ []
  matchChildren [] (_ ∷ _) _ _ = []
  matchChildren (_ ∷ _) [] _ _ = []
  matchChildren (childPattern ∷ remainingPatterns) (child ∷ children) graph sub =
    concatMap
      (λ next -> matchChildren remainingPatterns children graph next)
      (matchPattern childPattern child graph sub)

eMatch : Pattern -> Nat -> EGraph -> List Substitution
eMatch searchPattern classId graph =
  matchPattern searchPattern classId graph (MkSubstitution [])

mutual
  instantiatePattern :
    Pattern -> Substitution -> EGraph -> Maybe (Nat × EGraph)
  instantiatePattern (PatternVar name) sub graph =
    case lookupSubstitution name sub of λ where
      Nothing -> Nothing
      (Just id) -> Just (id , graph)
  instantiatePattern (PatternApp symbol patterns) sub graph =
    case instantiatePatterns patterns sub graph of λ where
      Nothing -> Nothing
      (Just (ids , graph')) -> Just (hashconsNode (MkENode symbol ids) graph')

  instantiatePatterns :
    List Pattern -> Substitution -> EGraph ->
    Maybe (List Nat × EGraph)
  instantiatePatterns [] _ graph = Just ([] , graph)
  instantiatePatterns (currentPattern ∷ remainingPatterns) sub graph =
    case instantiatePattern currentPattern sub graph of λ where
      Nothing -> Nothing
      (Just (id , graph')) ->
        case instantiatePatterns remainingPatterns sub graph' of λ where
          Nothing -> Nothing
          (Just (ids , graph'')) -> Just (id ∷ ids , graph'')

applyMatch :
  RewriteRule -> Nat -> Substitution -> EGraph -> EGraph × Nat
applyMatch rule rootId sub graph =
  case instantiatePattern (rhs rule) sub graph of λ where
    Nothing -> graph , 0
    (Just (rhsId , graph')) ->
      let left = root graph' rootId
          right = root graph' rhsId
      in if left == right then graph' , 0
         else mergeRoots left right graph' , incrementEGraphNat 0

applySubstitutions :
  List Substitution -> RewriteRule -> Nat -> EGraph -> Nat ->
  EGraph × Nat
applySubstitutions [] _ _ graph count = graph , count
applySubstitutions (sub ∷ rest) rule rootId graph count =
  let (graph' , changed) = applyMatch rule rootId sub graph in
  applySubstitutions rest rule rootId graph' (count + changed)

applyRuleToRoot :
  RewriteRule -> Nat -> EGraph -> EGraph × Nat
applyRuleToRoot rule rootId graph =
  applySubstitutions
    (eMatch (lhs rule) rootId graph)
    rule
    rootId
    graph
    0

uniqueRoots :
  List Binding -> EGraph -> List Nat -> List Nat
uniqueRoots [] _ seen = reverse seen
uniqueRoots (MkBinding _ id ∷ rest) graph seen =
  let r = root graph id in
  if memberNat r seen then uniqueRoots rest graph seen
  else uniqueRoots rest graph (r ∷ seen)

rootClasses : EGraph -> List Nat
rootClasses graph = uniqueRoots (bindings graph) graph []

applyRulesToRoots :
  RewriteRule -> List Nat -> EGraph -> EGraph × Nat
applyRulesToRoots _ [] graph = graph , 0
applyRulesToRoots rule (rootId ∷ roots) graph =
  let (graph' , count) = applyRuleToRoot rule rootId graph
      (graph'' , tailCount) = applyRulesToRoots rule roots graph'
  in graph'' , count + tailCount

saturatePass :
  List RewriteRule -> List Nat -> EGraph -> EGraph × Nat
saturatePass [] _ graph = graph , 0
saturatePass (rule ∷ rules) roots graph =
  let (graph' , count) = applyRulesToRoots rule roots graph
      (graph'' , tailCount) = saturatePass rules roots graph'
  in graph'' , count + tailCount

classCount : EGraph -> Nat
classCount graph = natListCount (rootClasses graph)

enodeCount : EGraph -> Nat
enodeCount graph = bindingCount (bindings graph)

-- One saturation result is represented as a record, not a wide tuple:
-- Agda2HS supports record extraction consistently across its Haskell targets.
record SaturationStep : Type where
  no-eta-equality; pattern
  constructor MkSaturationStep
  field
    stepGraph : EGraph
    stepTotalRewrites : Nat
    stepIterations : Nat
    stepComplete : Bool

open SaturationStep public

-- Saturation has a finite graph-sized iteration budget. Stable means a pass
-- performed no rewrites and rebuilding left class/enode counts unchanged.
saturateWithFuel :
  List ⊤ -> List RewriteRule -> EGraph -> Nat -> Nat -> SaturationStep
saturateWithFuel [] _ graph total iterations =
  MkSaturationStep graph total iterations False
saturateWithFuel (_ ∷ fuel) rules graph total iterations =
  let roots = rootClasses graph
      (graph' , rewrites) = saturatePass rules roots graph
      graph'' = rebuild graph'
      stable =
        rewrites == 0 &&
        classCount graph == classCount graph'' &&
        enodeCount graph == enodeCount graph''
      nextIterations = incrementEGraphNat iterations
  in if stable then
       MkSaturationStep graph'' (total + rewrites) nextIterations True
     else
       saturateWithFuel fuel rules graph'' (total + rewrites) nextIterations

saturateUntilStable :
  List RewriteRule -> EGraph -> EGraph × SaturationReport
saturateUntilStable rules graph =
  let result = saturateWithFuel (graphFuel graph) rules graph 0 0
      graph' = stepGraph result
      rewrites = stepTotalRewrites result
      iterations = stepIterations result
      complete = stepComplete result
      changed = if rewrites == 0 then False else True
  in graph' ,
     MkSaturationReport iterations rewrites changed complete

stringLength : String -> Nat
stringLength [] = 0
stringLength (_ ∷ rest) = incrementEGraphNat (stringLength rest)

stringLengthRegression : Bool
stringLengthRegression =
  stringLength "Agda" == incrementEGraphNat (incrementEGraphNat (incrementEGraphNat (incrementEGraphNat 0)))

stringLengthRegressionChecked : stringLengthRegression ≡ True
stringLengthRegressionChecked = refl

localCost : ENode -> Nat
localCost (MkENode symbol children) =
  incrementEGraphNat (stringLength symbol + natListCount children)

classAnalysisFor :
  Nat -> List Binding -> EGraph -> Maybe ClassAnalysis
classAnalysisFor target [] _ = Nothing
classAnalysisFor target (MkBinding node id ∷ rest) graph =
  case root graph id == target of λ where
    False -> classAnalysisFor target rest graph
    True ->
      case classAnalysisFor target rest graph of λ where
        Nothing ->
          Just (MkClassAnalysis target (incrementEGraphNat 0) (localCost node))
        (Just current) ->
          let nextCount = incrementEGraphNat (analysisENodeCount current)
              cost = localCost node
              nextCost =
                case cost < analysisMinLocalCost current of λ where
                  True -> cost
                  False -> analysisMinLocalCost current
          in Just (MkClassAnalysis target nextCount nextCost)

analyzeRoots : List Nat -> EGraph -> List ClassAnalysis
analyzeRoots [] _ = []
analyzeRoots (rootId ∷ roots) graph =
  case classAnalysisFor rootId (bindings graph) graph of λ where
    Nothing -> analyzeRoots roots graph
    (Just result) -> result ∷ analyzeRoots roots graph

analyze : EGraph -> List ClassAnalysis
analyze graph = analyzeRoots (rootClasses graph) graph

predNat : Nat -> Nat
predNat n = monusNat n 1

chooseCheaper : Maybe Extraction -> Maybe Extraction -> Maybe Extraction
chooseCheaper Nothing other = other
chooseCheaper other Nothing = other
chooseCheaper (Just left) (Just right) =
  if extractedCost left < extractedCost right then Just left else Just right

mutual
  -- Extraction fuel is a lazy list of unit tokens. Repeated binding-sized
  -- spines yield the same cubic upper bound used by the original extractor,
  -- without pattern matching on built-in Nat in runtime code.
  repeatFuel : List Binding -> List ⊤ -> List ⊤
  repeatFuel [] _ = []
  repeatFuel (_ ∷ rest) values = values ++ repeatFuel rest values

  extractFuelFor : EGraph -> List ⊤
  extractFuelFor graph =
    let bindingsFuel = unitFuel (bindings graph)
    in tt ∷ repeatFuel (bindings graph) (repeatFuel (bindings graph) bindingsFuel)

  extractBestSeen :
      List ⊤ -> Nat -> EGraph -> List Nat -> Maybe Extraction
  extractBestSeen [] _ _ _ = Nothing
  extractBestSeen (_ ∷ fuel) classId graph seen =
    let target = root graph classId
    in case memberNat target seen of λ where
      True -> Nothing
      False ->
        bestBindingForRoot
          fuel
          target
          (bindings graph)
          graph
          (target ∷ seen)

  extractChildren :
      List ⊤ -> List Nat -> EGraph -> List Nat -> Maybe ChildExtraction
  extractChildren _ [] _ _ = Just (MkChildExtraction [] 0)
  extractChildren [] (_ ∷ _) _ _ = Nothing
  extractChildren (_ ∷ fuel) (child ∷ children) graph seen =
    case extractBestSeen fuel child graph seen of λ where
      Nothing -> Nothing
      (Just first) ->
        case extractChildren fuel children graph seen of λ where
          Nothing -> Nothing
          (Just rest) ->
            Just
              (MkChildExtraction
                (extractedExpr first ∷ extractedChildren rest)
                (extractedCost first + extractedCostSum rest))

  bestBindingForRoot :
      List ⊤ -> Nat -> List Binding -> EGraph -> List Nat -> Maybe Extraction
  bestBindingForRoot _ _ [] _ _ = Nothing
  bestBindingForRoot [] _ (_ ∷ _) _ _ = Nothing
  bestBindingForRoot (_ ∷ fuel) target
    (MkBinding (MkENode symbol children) id ∷ rest)
    graph
    seen =
    case root graph id == target of λ where
      False ->
        bestBindingForRoot fuel target rest graph seen
      True ->
        let candidate =
              case extractChildren fuel children graph seen of λ where
                Nothing -> Nothing
                (Just children') ->
                  Just
                    (MkExtraction
                      (ExprApp symbol (extractedChildren children'))
                      (localCost (MkENode symbol children) +
                       extractedCostSum children'))
        in chooseCheaper candidate
             (bestBindingForRoot fuel target rest graph seen)

extractBest : Nat -> EGraph -> List ⊤ -> Maybe Extraction
extractBest classId graph fuel = extractBestSeen fuel classId graph []
associativityRule : RewriteRule
associativityRule =
  MkRewriteRule
    "proof-compose-associativity"
    (PatternApp "proof-compose"
      (PatternVar "A" ∷
       PatternApp "proof-compose" (PatternVar "B" ∷ PatternVar "C" ∷ []) ∷
       []))
    (PatternApp "proof-compose"
      (PatternApp "proof-compose"
        (PatternVar "A" ∷ PatternVar "B" ∷ []) ∷
       PatternVar "C" ∷ []))

emptyRightRule : RewriteRule
emptyRightRule =
  MkRewriteRule
    "proof-compose-empty-right"
    (PatternApp "proof-compose"
      (PatternVar "A" ∷
       PatternApp "empty-proof-compose" [] ∷
       []))
    (PatternVar "A")

emptyLeftRule : RewriteRule
emptyLeftRule =
  MkRewriteRule
    "proof-compose-empty-left"
    (PatternApp "proof-compose"
      (PatternApp "empty-proof-compose" [] ∷
       PatternVar "A" ∷
       []))
    (PatternVar "A")

-- Symbolic tags for the three requested constructive/domain traditions.
-- These normalize named assumptions for graph search; they are not added
-- Agda kernel axioms and do not alone prove learner optimality.
russianConstructivismPostulateRule : RewriteRule
russianConstructivismPostulateRule =
  MkRewriteRule
    "russian-constructivism-postulate"
    (PatternApp "constructivist-postulate"
      (PatternApp "RussianConstructivism" [] ∷ []))
    (PatternApp "constructive-framework"
      (PatternApp "RussianConstructivism" [] ∷ []))

scottErshovDenotationalSemanticsPostulateRule : RewriteRule
scottErshovDenotationalSemanticsPostulateRule =
  MkRewriteRule
    "scott-ershov-denotational-semantics-postulate"
    (PatternApp "constructivist-postulate"
      (PatternApp "ScottErshovDomainSemantics" [] ∷ []))
    (PatternApp "domain-denotational-semantics"
      (PatternApp "ScottErshovDomainSemantics" [] ∷ []))

bishopConstructivismPostulateRule : RewriteRule
bishopConstructivismPostulateRule =
  MkRewriteRule
    "bishop-constructivism-postulate"
    (PatternApp "constructivist-postulate"
      (PatternApp "BishopConstructivism" [] ∷ []))
    (PatternApp "constructive-proof-method"
      (PatternApp "BishopConstructivism" [] ∷ []))

semanticRewriteRules : List RewriteRule
semanticRewriteRules =
  associativityRule ∷
  emptyRightRule ∷
  emptyLeftRule ∷
  russianConstructivismPostulateRule ∷
  scottErshovDenotationalSemanticsPostulateRule ∷
  bishopConstructivismPostulateRule ∷
  []

constructivistPostulateRegression : Bool
constructivistPostulateRegression =
  let
    russian =
      ExprApp "constructivist-postulate"
        (ExprApp "RussianConstructivism" [] ∷ [])
    russianNormalized =
      ExprApp "constructive-framework"
        (ExprApp "RussianConstructivism" [] ∷ [])
    scottErshov =
      ExprApp "constructivist-postulate"
        (ExprApp "ScottErshovDomainSemantics" [] ∷ [])
    scottErshovNormalized =
      ExprApp "domain-denotational-semantics"
        (ExprApp "ScottErshovDomainSemantics" [] ∷ [])
    bishop =
      ExprApp "constructivist-postulate"
        (ExprApp "BishopConstructivism" [] ∷ [])
    bishopNormalized =
      ExprApp "constructive-proof-method"
        (ExprApp "BishopConstructivism" [] ∷ [])
    (russianId , g1) = addExpr russian emptyGraph
    (russianNormalizedId , g2) = addExpr russianNormalized g1
    (scottErshovId , g3) = addExpr scottErshov g2
    (scottErshovNormalizedId , g4) = addExpr scottErshovNormalized g3
    (bishopId , g5) = addExpr bishop g4
    (bishopNormalizedId , g6) = addExpr bishopNormalized g5
    (saturated , report) = saturateUntilStable semanticRewriteRules g6
  in
  saturationComplete report
    && equivalent russianId russianNormalizedId saturated
    && equivalent scottErshovId scottErshovNormalizedId saturated
    && equivalent bishopId bishopNormalizedId saturated

constructivistPostulateRegression-proof :
  constructivistPostulateRegression ≡ True
constructivistPostulateRegression-proof = refl

lawExpr : String -> Expr
lawExpr id = ExprApp "semantic-law" (ExprAtom id ∷ [])

leftAssocExprAcc : Expr -> List String -> Expr
leftAssocExprAcc acc [] = acc
leftAssocExprAcc acc (id ∷ rest) =
  leftAssocExprAcc
    (ExprApp "proof-compose" (acc ∷ lawExpr id ∷ []))
    rest

leftAssocExpr : List String -> Expr
leftAssocExpr [] = ExprAtom "empty-proof-compose"
leftAssocExpr (id ∷ []) = lawExpr id
leftAssocExpr (a ∷ b ∷ rest) =
  leftAssocExprAcc
    (ExprApp "proof-compose" (lawExpr a ∷ lawExpr b ∷ []))
    rest

rightAssocExpr : List String -> Expr
rightAssocExpr [] = ExprAtom "empty-proof-compose"
rightAssocExpr (id ∷ []) = lawExpr id
rightAssocExpr (a ∷ b ∷ rest) =
  ExprApp "proof-compose"
    (lawExpr a ∷ rightAssocExpr (b ∷ rest) ∷ [])

emptyGraph : EGraph
emptyGraph = MkEGraph 0 [] []

record EGraphRegression : Type where
  no-eta-equality; pattern
  constructor MkEGraphRegression
  field
    regressionStableGraph : EGraph
    regressionCongruenceOk : Bool
    regressionAssociativityOk : Bool
    regressionRightIdentityOk : Bool
    regressionLeftIdentityOk : Bool
    regressionMatchingOk : Bool
    regressionAnalysisOk : Bool
    regressionExtractOk : Bool
    regressionQuotientOk : Bool
    regressionIterationOk : Bool
    regressionSaturationOk : Bool

open EGraphRegression public

-- After a union, stored enodes must be interpreted through the current
-- representatives. This checks the invariant even before rebuild is called.
bindingsCanonical : List Binding -> EGraph -> Bool
bindingsCanonical [] _ = True
bindingsCanonical (MkBinding node _ ∷ rest) graph =
  sameENode node (canonicalNode graph node) && bindingsCanonical rest graph

canonicalBindingsRegression : Bool
canonicalBindingsRegression =
  let (a , g1) = addExpr (ExprAtom "a") emptyGraph
      (b , g2) = addExpr (ExprAtom "b") g1
      (_ , g3) = addExpr (ExprApp "f" (ExprAtom "b" ∷ [])) g2
      g4 = merge a b g3
  in bindingsCanonical (bindings g4) g4

canonicalBindingsRegression-proof : canonicalBindingsRegression ≡ True
canonicalBindingsRegression-proof = refl

-- A rewrite pass may union classes before its rebuild pass. Hash-consing at
-- that seam must compare existing enodes modulo the current union-find roots.
hashconsAfterUnionRegression : Bool
hashconsAfterUnionRegression =
  let (a , g1) = addExpr (ExprAtom "a") emptyGraph
      (b , g2) = addExpr (ExprAtom "b") g1
      (fb , g3) = addExpr (ExprApp "f" (ExprAtom "b" ∷ [])) g2
      g4 = mergeRoots a b g3
      before = enodeCount g4
      (fa , g5) = addExpr (ExprApp "f" (ExprAtom "a" ∷ [])) g4
  in enodeCount g5 == before && equivalent fa fb g5

hashconsAfterUnionRegression-proof : hashconsAfterUnionRegression ≡ True
hashconsAfterUnionRegression-proof = refl

regressionGraph : EGraphRegression
regressionGraph =
  let (a , g1) = addExpr (ExprAtom "a") emptyGraph
      (b , g2) = addExpr (ExprAtom "b") g1
      (fa , g3) = addExpr (ExprApp "f" (ExprAtom "a" ∷ [])) g2
      (fb , g4) = addExpr (ExprApp "f" (ExprAtom "b" ∷ [])) g3
      g5 = merge a b g4
      (nested , g6) =
        addExpr
          (ExprApp "proof-compose"
            (ExprAtom "a" ∷
             ExprApp "proof-compose" (ExprAtom "b" ∷ ExprAtom "c" ∷ []) ∷ []))
          g5
      (left , g7) =
        addExpr
          (ExprApp "proof-compose"
            (ExprApp "proof-compose" (ExprAtom "a" ∷ ExprAtom "b" ∷ []) ∷
             ExprAtom "c" ∷ []))
          g6
      (stable , report) =
        saturateUntilStable semanticRewriteRules g7
      congruenceOk =
        equivalent fa fb g5
      associativityOk =
        equivalent nested left stable
      rightIdentityExpr =
        ExprApp "proof-compose"
          (ExprAtom "a" ∷ ExprAtom "empty-proof-compose" ∷ [])
      (rightIdentity , g8) =
        addExpr rightIdentityExpr stable
      (aAgain , g9) =
        addExpr (ExprAtom "a") g8
      (rightStable , rightReport) =
        saturateUntilStable semanticRewriteRules g9
      rightIdentityOk =
        equivalent rightIdentity aAgain rightStable
      leftIdentityExpr =
        ExprApp "proof-compose"
          (ExprAtom "empty-proof-compose" ∷ ExprAtom "a" ∷ [])
      (leftIdentity , g10) =
        addExpr leftIdentityExpr rightStable
      (aAgainLeft , g11) =
        addExpr (ExprAtom "a") g10
      (leftStable , leftReport) =
        saturateUntilStable semanticRewriteRules g11
      leftIdentityOk =
        equivalent leftIdentity aAgainLeft leftStable
      matchingOk =
        case eMatch
          (PatternApp "proof-compose"
            (PatternVar "X" ∷
             PatternApp "proof-compose"
               (PatternVar "Y" ∷ PatternVar "Z" ∷ []) ∷ []))
          nested
          stable of λ where
            [] -> False
            _ -> True
      analysisOk = classAnalysisCount (analyze stable) > 0
      extractOk =
        case extractBest nested stable (extractFuelFor stable) of λ where
          Nothing -> False
          (Just result) -> extractedCost result > 0
      quotientOk = classCount g5 < enodeCount g5
      iterationOk = saturationIterations report > 0
      saturationOk =
        saturationComplete report &&
        saturationComplete rightReport &&
        saturationComplete leftReport
  in MkEGraphRegression
       stable
       congruenceOk
       associativityOk
       rightIdentityOk
       leftIdentityOk
       matchingOk
       analysisOk
       extractOk
       quotientOk
       iterationOk
       saturationOk

regressionCongruence-proof :
  regressionCongruenceOk regressionGraph ≡ True
regressionCongruence-proof = refl

regressionAssociativity-proof :
  regressionAssociativityOk regressionGraph ≡ True
regressionAssociativity-proof = refl

regressionRightIdentity-proof :
  regressionRightIdentityOk regressionGraph ≡ True
regressionRightIdentity-proof = refl

regressionLeftIdentity-proof :
  regressionLeftIdentityOk regressionGraph ≡ True
regressionLeftIdentity-proof = refl

regressionMatching-proof :
  regressionMatchingOk regressionGraph ≡ True
regressionMatching-proof = refl

regressionAnalysis-proof :
  regressionAnalysisOk regressionGraph ≡ True
regressionAnalysis-proof = refl

regressionExtraction-proof :
  regressionExtractOk regressionGraph ≡ True
regressionExtraction-proof = refl

regressionQuotient-proof :
  regressionQuotientOk regressionGraph ≡ True
regressionQuotient-proof = refl

regressionIterations-proof :
  regressionIterationOk regressionGraph ≡ True
regressionIterations-proof = refl

regressionSaturation-proof :
  regressionSaturationOk regressionGraph ≡ True
regressionSaturation-proof = refl

symbolicEGraphRegression : Bool
symbolicEGraphRegression =
  regressionCongruenceOk regressionGraph &&
  regressionAssociativityOk regressionGraph &&
  regressionRightIdentityOk regressionGraph &&
  regressionLeftIdentityOk regressionGraph &&
  regressionMatchingOk regressionGraph &&
  regressionAnalysisOk regressionGraph &&
  regressionExtractOk regressionGraph &&
  regressionQuotientOk regressionGraph &&
  regressionIterationOk regressionGraph &&
  regressionSaturationOk regressionGraph &&
  canonicalBindingsRegression &&
  hashconsAfterUnionRegression

symbolicEGraphRegression-proof :
  symbolicEGraphRegression ≡ True
symbolicEGraphRegression-proof = refl

eGraphAssociativityRegression : Bool
eGraphAssociativityRegression = regressionAssociativityOk regressionGraph

eGraphAssociativityRegression-proof :
  eGraphAssociativityRegression ≡ True
eGraphAssociativityRegression-proof = refl


-- Public extraction roots consumed by the semantic-search executable.
{-# COMPILE AGDA2HS Expr #-}
{-# COMPILE AGDA2HS Pattern #-}
{-# COMPILE AGDA2HS RewriteRule #-}
{-# COMPILE AGDA2HS ENode #-}
{-# COMPILE AGDA2HS Binding #-}
{-# COMPILE AGDA2HS EGraph #-}
{-# COMPILE AGDA2HS Substitution #-}
{-# COMPILE AGDA2HS ClassAnalysis #-}
{-# COMPILE AGDA2HS SaturationReport #-}
{-# COMPILE AGDA2HS SaturationStep #-}
{-# COMPILE AGDA2HS Extraction #-}
{-# COMPILE AGDA2HS ChildExtraction #-}
{-# COMPILE AGDA2HS unitFuel #-}
{-# COMPILE AGDA2HS graphFuel #-}
{-# COMPILE AGDA2HS repeatFuel #-}
{-# COMPILE AGDA2HS extractFuelFor #-}
{-# COMPILE AGDA2HS sameENode #-}
{-# COMPILE AGDA2HS freshClass #-}
{-# COMPILE AGDA2HS emptyGraph #-}
{-# COMPILE AGDA2HS lawExpr #-}
{-# COMPILE AGDA2HS leftAssocExprAcc #-}
{-# COMPILE AGDA2HS leftAssocExpr #-}
{-# COMPILE AGDA2HS rightAssocExpr #-}
{-# COMPILE AGDA2HS EGraphRegression #-}
{-# COMPILE AGDA2HS saturateUntilStable #-}
{-# COMPILE AGDA2HS saturateWithFuel #-}
{-# COMPILE AGDA2HS saturatePass #-}
{-# COMPILE AGDA2HS applyRulesToRoots #-}
{-# COMPILE AGDA2HS applyRuleToRoot #-}
{-# COMPILE AGDA2HS applySubstitutions #-}
{-# COMPILE AGDA2HS applyMatch #-}
{-# COMPILE AGDA2HS instantiatePattern #-}
{-# COMPILE AGDA2HS instantiatePatterns #-}
{-# COMPILE AGDA2HS eMatch #-}
{-# COMPILE AGDA2HS rootClasses #-}
{-# COMPILE AGDA2HS root #-}
{-# COMPILE AGDA2HS rebuild #-}
{-# COMPILE AGDA2HS classCount #-}
{-# COMPILE AGDA2HS enodeCount #-}
{-# COMPILE AGDA2HS analyze #-}
{-# COMPILE AGDA2HS extractBest #-}
{-# COMPILE AGDA2HS rootWithFuel #-}
{-# COMPILE AGDA2HS rebuildWithFuel #-}
{-# COMPILE AGDA2HS canonicalizeBindings #-}
{-# COMPILE AGDA2HS bindingsCanonical #-}
{-# COMPILE AGDA2HS canonicalBindingsRegression #-}
{-# COMPILE AGDA2HS hashconsAfterUnionRegression #-}
{-# COMPILE AGDA2HS rebuildPass #-}
{-# COMPILE AGDA2HS rebuildBindings #-}
{-# COMPILE AGDA2HS mergeRoots #-}
{-# COMPILE AGDA2HS addExpr #-}
{-# COMPILE AGDA2HS addExprs #-}
{-# COMPILE AGDA2HS hashconsNode #-}
{-# COMPILE AGDA2HS findBindingByNode #-}
{-# COMPILE AGDA2HS canonicalNode #-}
{-# COMPILE AGDA2HS canonicalChildren #-}
{-# COMPILE AGDA2HS parentsLookup #-}
{-# COMPILE AGDA2HS uniqueRoots #-}
{-# COMPILE AGDA2HS memberNat #-}
{-# COMPILE AGDA2HS natListCount #-}
{-# COMPILE AGDA2HS bindingCount #-}
{-# COMPILE AGDA2HS classAnalysisCount #-}
{-# COMPILE AGDA2HS localCost #-}
{-# COMPILE AGDA2HS lookupSubstitution #-}
{-# COMPILE AGDA2HS bindSubstitution #-}
{-# COMPILE AGDA2HS matchPattern #-}
{-# COMPILE AGDA2HS matchNodes #-}
{-# COMPILE AGDA2HS matchChildren #-}
{-# COMPILE AGDA2HS extractBestSeen #-}
{-# COMPILE AGDA2HS extractChildren #-}
{-# COMPILE AGDA2HS bestBindingForRoot #-}
{-# COMPILE AGDA2HS chooseCheaper #-}
{-# COMPILE AGDA2HS classAnalysisFor #-}
{-# COMPILE AGDA2HS analyzeRoots #-}
{-# COMPILE AGDA2HS predNat #-}
{-# COMPILE AGDA2HS incrementEGraphNat #-}
{-# COMPILE AGDA2HS stringLength #-}
{-# COMPILE AGDA2HS setPair #-}
{-# COMPILE AGDA2HS listEqualNat #-}
{-# COMPILE AGDA2HS natEqual #-}
{-# COMPILE AGDA2HS lookupNatPair #-}
{-# COMPILE AGDA2HS lookupStringPair #-}
{-# COMPILE AGDA2HS findOtherNode #-}
{-# COMPILE AGDA2HS semanticRewriteRules #-}
{-# COMPILE AGDA2HS associativityRule #-}
{-# COMPILE AGDA2HS emptyRightRule #-}
{-# COMPILE AGDA2HS emptyLeftRule #-}
{-# COMPILE AGDA2HS russianConstructivismPostulateRule #-}
{-# COMPILE AGDA2HS scottErshovDenotationalSemanticsPostulateRule #-}
{-# COMPILE AGDA2HS bishopConstructivismPostulateRule #-}
{-# COMPILE AGDA2HS constructivistPostulateRegression #-}
{-# COMPILE AGDA2HS equivalent #-}
{-# COMPILE AGDA2HS merge #-}
{-# COMPILE AGDA2HS regressionGraph #-}

{-# COMPILE AGDA2HS symbolicEGraphRegression #-}
{-# COMPILE AGDA2HS eGraphAssociativityRegression #-}
