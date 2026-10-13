module FullCoupled.Agda2HsTheoremGraphEGraph where

open import Haskell.Prelude


data Expr : Type where
  atom : String -> Expr
  app : String -> List Expr -> Expr

data Pattern : Type where
  pvar : String -> Pattern
  papp : String -> List Pattern -> Pattern

record RewriteRule : Type where
  constructor rewriteRule
  field
    ruleName : String
    lhs : Pattern
    rhs : Pattern

open RewriteRule public

record ENode : Type where
  constructor enode
  field
    symbol : String
    children : List Nat

open ENode public

record Binding : Type where
  constructor binding
  field
    node : ENode
    classId : Nat

open Binding public

bindingCount : List Binding -> Nat
bindingCount [] = zero
bindingCount (_ ∷ rest) = suc (bindingCount rest)

natListCount : List Nat -> Nat
natListCount [] = zero
natListCount (_ ∷ rest) = suc (natListCount rest)

bindingCountRegression : Bool
bindingCountRegression =
  bindingCount [] == zero
  && bindingCount (binding (enode "atom" []) zero ∷ []) == suc zero

bindingCountRegressionChecked : bindingCountRegression ≡ True
bindingCountRegressionChecked = refl

record EGraph : Type where
  constructor egraph
  field
    nextId : Nat
    parents : List (Nat × Nat)
    bindings : List Binding

open EGraph public

record Substitution : Type where
  constructor substitution
  field
    entries : List (String × Nat)

open Substitution public

record ClassAnalysis : Type where
  constructor classAnalysis
  field
    analysisClass : Nat
    analysisENodeCount : Nat
    analysisMinLocalCost : Nat

open ClassAnalysis public

classAnalysisCount : List ClassAnalysis -> Nat
classAnalysisCount [] = zero
classAnalysisCount (_ ∷ rest) = suc (classAnalysisCount rest)

record SaturationReport : Type where
  constructor saturationReport
  field
    saturationIterations : Nat
    saturationRewrites : Nat
    saturationChanged : Bool
    saturationComplete : Bool

open SaturationReport public

record Extraction : Type where
  constructor extraction
  field
    extractedExpr : Expr
    extractedCost : Nat

open Extraction public

record ChildExtraction : Type where
  constructor childExtraction
  field
    extractedChildren : List Expr
    extractedCostSum : Nat

open ChildExtraction public

memberNat : Nat -> List Nat -> Bool
memberNat _ [] = False
memberNat x (y ∷ ys) =
  if x == y then True else memberNat x ys

natEqual : Nat -> Nat -> Bool
natEqual zero zero = True
natEqual zero (suc _) = False
natEqual (suc _) zero = False
natEqual (suc left) (suc right) = natEqual left right

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

setPair : {A B : Type} -> A -> B -> List (A × B) -> List (A × B)
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

rootWithFuel : Nat -> Nat -> List (Nat × Nat) -> Nat
rootWithFuel zero id _ = id
rootWithFuel (suc fuel) id parents =
  let parent = parentsLookup id parents in
  if parent == id then id else rootWithFuel fuel parent parents

root : EGraph -> Nat -> Nat
root graph id = rootWithFuel (suc (nextId graph)) id (parents graph)

canonicalChildren : EGraph -> List Nat -> List Nat
canonicalChildren _ [] = []
canonicalChildren graph (x ∷ xs) =
  root graph x ∷ canonicalChildren graph xs

canonicalNode : EGraph -> ENode -> ENode
canonicalNode graph (enode symbol children) =
  enode symbol (canonicalChildren graph children)

sameENode : ENode -> ENode -> Bool
sameENode (enode sx xs) (enode sy ys) =
  if sx == sy then listEqualNat xs ys else False

findBindingByNode : ENode -> List Binding -> Maybe Nat
findBindingByNode _ [] = Nothing
findBindingByNode target (binding candidate id ∷ rest) =
  if sameENode target candidate then Just id
  else findBindingByNode target rest

freshClass : EGraph -> Nat × EGraph
freshClass graph =
  let id = nextId graph
      graph' = egraph (suc id) (setPair id id (parents graph)) (bindings graph)
  in id , graph'

hashconsNode : ENode -> EGraph -> Nat × EGraph
hashconsNode raw graph =
  let node = canonicalNode graph raw in
  case findBindingByNode node (bindings graph) of λ where
    Nothing ->
      let (id , graph') = freshClass graph in
      id ,
      egraph
        (nextId graph')
        (parents graph')
        (binding node id ∷ bindings graph')
    (Just id) -> root graph id , graph

mutual
  addExpr : Expr -> EGraph -> Nat × EGraph
  addExpr (atom symbol) graph =
    hashconsNode (enode symbol []) graph
  addExpr (app symbol children) graph =
    let (childIds , graph') = addExprs children graph in
    hashconsNode (enode symbol childIds) graph'

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
    in egraph (nextId graph) (setPair large small (parents graph)) (bindings graph)

equivalent : Nat -> Nat -> EGraph -> Bool
equivalent left right graph = root graph left == root graph right

findOtherNode :
  ENode -> Nat -> EGraph -> List Binding -> Maybe Nat
findOtherNode _ _ _ [] = Nothing
findOtherNode target excluded graph (binding candidate id ∷ rest) =
  if id == excluded then findOtherNode target excluded graph rest
  else if sameENode target (canonicalNode graph candidate) then Just id
  else findOtherNode target excluded graph rest

rebuildBindings :
  List Binding -> EGraph -> Bool -> EGraph × Bool
rebuildBindings [] graph changed = graph , changed
rebuildBindings (binding node id ∷ rest) graph changed =
  let canonical = canonicalNode graph node
  in
  case findOtherNode canonical id graph (bindings graph) of λ where
    Nothing -> rebuildBindings rest graph changed
    (Just other) ->
      if equivalent id other graph then
        rebuildBindings rest graph changed
      else
        rebuildBindings rest (mergeRoots id other graph) True

rebuildPass : EGraph -> EGraph × Bool
rebuildPass graph =
  rebuildBindings (bindings graph) graph False

rebuildWithFuel : Nat -> EGraph -> EGraph
rebuildWithFuel zero graph = graph
rebuildWithFuel (suc fuel) graph =
  let (graph' , changed) = rebuildPass graph in
  if changed then rebuildWithFuel fuel graph' else graph'

rebuild : EGraph -> EGraph
rebuild graph = rebuildWithFuel (suc (bindingCount (bindings graph))) graph

merge : Nat -> Nat -> EGraph -> EGraph
merge left right graph = rebuild (mergeRoots left right graph)

lookupSubstitution : String -> Substitution -> Maybe Nat
lookupSubstitution name (substitution entries) = lookupStringPair name entries

bindSubstitution : String -> Nat -> Substitution -> Maybe Substitution
bindSubstitution name id (substitution entries) =
  case lookupSubstitution name (substitution entries) of λ where
    Nothing -> Just (substitution ((name , id) ∷ entries))
    (Just old) ->
      if old == id then Just (substitution entries) else Nothing

mutual
  matchPattern :
    Pattern -> Nat -> EGraph -> Substitution -> List Substitution
  matchPattern (pvar name) class graph sub =
    case bindSubstitution name (root graph class) sub of λ where
      Nothing -> []
      (Just result) -> result ∷ []
  matchPattern (papp symbol patterns) class graph sub =
    matchNodes symbol patterns (root graph class) graph (bindings graph) sub

  matchNodes :
    String -> List Pattern -> Nat -> EGraph ->
    List Binding -> Substitution -> List Substitution
  matchNodes _ _ _ _ [] _ = []
  matchNodes symbol patterns target graph
    (binding (enode candidate children) class ∷ rest) sub =
    if root graph class == target then
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
eMatch searchPattern class graph =
  matchPattern searchPattern class graph (substitution [])

mutual
  instantiatePattern :
    Pattern -> Substitution -> EGraph -> Maybe (Nat × EGraph)
  instantiatePattern (pvar name) sub graph =
    case lookupSubstitution name sub of λ where
      Nothing -> Nothing
      (Just id) -> Just (id , graph)
  instantiatePattern (papp symbol patterns) sub graph =
    case instantiatePatterns patterns sub graph of λ where
      Nothing -> Nothing
      (Just (ids , graph')) -> Just (hashconsNode (enode symbol ids) graph')

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
    Nothing -> graph , zero
    (Just (rhsId , graph')) ->
      let left = root graph' rootId
          right = root graph' rhsId
      in if left == right then graph' , zero
         else mergeRoots left right graph' , suc zero

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
    zero

uniqueRoots :
  List Binding -> EGraph -> List Nat -> List Nat
uniqueRoots [] _ seen = reverse seen
uniqueRoots (binding _ id ∷ rest) graph seen =
  let r = root graph id in
  if memberNat r seen then uniqueRoots rest graph seen
  else uniqueRoots rest graph (r ∷ seen)

rootClasses : EGraph -> List Nat
rootClasses graph = uniqueRoots (bindings graph) graph []

applyRulesToRoots :
  RewriteRule -> List Nat -> EGraph -> EGraph × Nat
applyRulesToRoots _ [] graph = graph , zero
applyRulesToRoots rule (rootId ∷ roots) graph =
  let (graph' , count) = applyRuleToRoot rule rootId graph
      (graph'' , tailCount) = applyRulesToRoots rule roots graph'
  in graph'' , count + tailCount

saturatePass :
  List RewriteRule -> List Nat -> EGraph -> EGraph × Nat
saturatePass [] _ graph = graph , zero
saturatePass (rule ∷ rules) roots graph =
  let (graph' , count) = applyRulesToRoots rule roots graph
      (graph'' , tailCount) = saturatePass rules roots graph'
  in graph'' , count + tailCount

classCount : EGraph -> Nat
classCount graph = natListCount (rootClasses graph)

enodeCount : EGraph -> Nat
enodeCount graph = bindingCount (bindings graph)

saturateWithFuel :
  Nat -> List RewriteRule -> EGraph -> Nat -> Nat -> EGraph × Nat × Nat × Bool
saturateWithFuel zero _ graph total iterations =
  graph , total , iterations , False
saturateWithFuel (suc fuel) rules graph total iterations =
  let roots = rootClasses graph
      (graph' , rewrites) = saturatePass rules roots graph
      graph'' = rebuild graph'
      stable =
        rewrites == zero &&
        classCount graph == classCount graph'' &&
        enodeCount graph == enodeCount graph''
      nextIterations = suc iterations
  in if stable then
       graph'' , total + rewrites , nextIterations , True
     else
       saturateWithFuel fuel rules graph'' (total + rewrites) nextIterations

saturateUntilStable :
  List RewriteRule -> EGraph -> EGraph × SaturationReport
saturateUntilStable rules graph =
  let (graph' , rewrites , iterations , complete) =
        saturateWithFuel (suc (enodeCount graph)) rules graph zero zero
      changed = if rewrites == zero then False else True
  in graph' ,
     saturationReport iterations rewrites changed complete

stringLength : String -> Nat
stringLength [] = zero
stringLength (_ ∷ rest) = suc (stringLength rest)

stringLengthRegression : Bool
stringLengthRegression =
  stringLength "Agda" == suc (suc (suc (suc zero)))

stringLengthRegressionChecked : stringLengthRegression ≡ True
stringLengthRegressionChecked = refl

localCost : ENode -> Nat
localCost (enode symbol children) =
  suc (stringLength symbol + natListCount children)

classAnalysisFor :
  Nat -> List Binding -> EGraph -> Maybe ClassAnalysis
classAnalysisFor target [] _ = Nothing
classAnalysisFor target (binding node id ∷ rest) graph =
  case root graph id == target of λ where
    False -> classAnalysisFor target rest graph
    True ->
      case classAnalysisFor target rest graph of λ where
        Nothing ->
          Just (classAnalysis target (suc zero) (localCost node))
        (Just current) ->
          let nextCount = suc (analysisENodeCount current)
              cost = localCost node
              nextCost =
                case cost < analysisMinLocalCost current of λ where
                  True -> cost
                  False -> analysisMinLocalCost current
          in Just (classAnalysis target nextCount nextCost)

analyzeRoots : List Nat -> EGraph -> List ClassAnalysis
analyzeRoots [] _ = []
analyzeRoots (rootId ∷ roots) graph =
  case classAnalysisFor rootId (bindings graph) graph of λ where
    Nothing -> analyzeRoots roots graph
    (Just result) -> result ∷ analyzeRoots roots graph

analyze : EGraph -> List ClassAnalysis
analyze graph = analyzeRoots (rootClasses graph) graph

predNat : Nat -> Nat
predNat zero = zero
predNat (suc n) = n

chooseCheaper : Maybe Extraction -> Maybe Extraction -> Maybe Extraction
chooseCheaper Nothing other = other
chooseCheaper other Nothing = other
chooseCheaper (Just left) (Just right) =
  if extractedCost left < extractedCost right then Just left else Just right

mutual
  extractBestSeen :
      Nat -> Nat -> EGraph -> List Nat -> Maybe Extraction
  extractBestSeen zero _ _ _ = Nothing
  extractBestSeen (suc fuel) class graph seen =
    let target = root graph class
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
      Nat -> List Nat -> EGraph -> List Nat -> Maybe ChildExtraction
  extractChildren _ [] _ _ = Just (childExtraction [] zero)
  extractChildren zero (_ ∷ _) _ _ = Nothing
  extractChildren (suc fuel) (child ∷ children) graph seen =
    case extractBestSeen fuel child graph seen of λ where
      Nothing -> Nothing
      (Just first) ->
        case extractChildren fuel children graph seen of λ where
          Nothing -> Nothing
          (Just rest) ->
            Just
              (childExtraction
                (extractedExpr first ∷ extractedChildren rest)
                (extractedCost first + extractedCostSum rest))

  bestBindingForRoot :
      Nat -> Nat -> List Binding -> EGraph -> List Nat -> Maybe Extraction
  bestBindingForRoot _ _ [] _ _ = Nothing
  bestBindingForRoot zero _ (_ ∷ _) _ _ = Nothing
  bestBindingForRoot (suc fuel) target
    (binding (enode symbol children) id ∷ rest)
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
                    (extraction
                      (app symbol (extractedChildren children'))
                      (localCost (enode symbol children) +
                       extractedCostSum children'))
        in chooseCheaper candidate
             (bestBindingForRoot fuel target rest graph seen)

extractBest : Nat -> EGraph -> Nat -> Maybe Extraction
extractBest class graph fuel = extractBestSeen fuel class graph []
associativityRule : RewriteRule
associativityRule =
  rewriteRule
    "proof-compose-associativity"
    (papp "proof-compose"
      (pvar "A" ∷
       papp "proof-compose" (pvar "B" ∷ pvar "C" ∷ []) ∷
       []))
    (papp "proof-compose"
      (papp "proof-compose"
        (pvar "A" ∷ pvar "B" ∷ []) ∷
       pvar "C" ∷ []))

emptyRightRule : RewriteRule
emptyRightRule =
  rewriteRule
    "proof-compose-empty-right"
    (papp "proof-compose"
      (pvar "A" ∷
       papp "empty-proof-compose" [] ∷
       []))
    (pvar "A")

emptyLeftRule : RewriteRule
emptyLeftRule =
  rewriteRule
    "proof-compose-empty-left"
    (papp "proof-compose"
      (papp "empty-proof-compose" [] ∷
       pvar "A" ∷
       []))
    (pvar "A")

semanticRewriteRules : List RewriteRule
semanticRewriteRules =
  associativityRule ∷
  emptyRightRule ∷
  emptyLeftRule ∷
  []

lawExpr : String -> Expr
lawExpr id = app "semantic-law" (atom id ∷ [])

leftAssocExprAcc : Expr -> List String -> Expr
leftAssocExprAcc acc [] = acc
leftAssocExprAcc acc (id ∷ rest) =
  leftAssocExprAcc
    (app "proof-compose" (acc ∷ lawExpr id ∷ []))
    rest

leftAssocExpr : List String -> Expr
leftAssocExpr [] = atom "empty-proof-compose"
leftAssocExpr (id ∷ []) = lawExpr id
leftAssocExpr (a ∷ b ∷ rest) =
  leftAssocExprAcc
    (app "proof-compose" (lawExpr a ∷ lawExpr b ∷ []))
    rest

rightAssocExpr : List String -> Expr
rightAssocExpr [] = atom "empty-proof-compose"
rightAssocExpr (id ∷ []) = lawExpr id
rightAssocExpr (a ∷ b ∷ rest) =
  app "proof-compose"
    (lawExpr a ∷ rightAssocExpr (b ∷ rest) ∷ [])

emptyGraph : EGraph
emptyGraph = egraph zero [] []

record EGraphRegression : Type where
  constructor egraphRegression
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

regressionGraph : EGraphRegression
regressionGraph =
  let (a , g1) = addExpr (atom "a") emptyGraph
      (b , g2) = addExpr (atom "b") g1
      (fa , g3) = addExpr (app "f" (atom "a" ∷ [])) g2
      (fb , g4) = addExpr (app "f" (atom "b" ∷ [])) g3
      g5 = merge a b g4
      (nested , g6) =
        addExpr
          (app "proof-compose"
            (atom "a" ∷
             app "proof-compose" (atom "b" ∷ atom "c" ∷ []) ∷ []))
          g5
      (left , g7) =
        addExpr
          (app "proof-compose"
            (app "proof-compose" (atom "a" ∷ atom "b" ∷ []) ∷
             atom "c" ∷ []))
          g6
      (stable , report) =
        saturateUntilStable semanticRewriteRules g7
      congruenceOk =
        equivalent fa fb g5
      associativityOk =
        equivalent nested left stable
      rightIdentityExpr =
        app "proof-compose"
          (atom "a" ∷ atom "empty-proof-compose" ∷ [])
      (rightIdentity , g8) =
        addExpr rightIdentityExpr stable
      (aAgain , g9) =
        addExpr (atom "a") g8
      (rightStable , rightReport) =
        saturateUntilStable semanticRewriteRules g9
      rightIdentityOk =
        equivalent rightIdentity aAgain rightStable
      leftIdentityExpr =
        app "proof-compose"
          (atom "empty-proof-compose" ∷ atom "a" ∷ [])
      (leftIdentity , g10) =
        addExpr leftIdentityExpr rightStable
      (aAgainLeft , g11) =
        addExpr (atom "a") g10
      (leftStable , leftReport) =
        saturateUntilStable semanticRewriteRules g11
      leftIdentityOk =
        equivalent leftIdentity aAgainLeft leftStable
      matchingOk =
        case eMatch
          (papp "proof-compose"
            (pvar "X" ∷
             papp "proof-compose"
               (pvar "Y" ∷ pvar "Z" ∷ []) ∷ []))
          nested
          stable of λ where
            [] -> False
            _ -> True
      analysisOk = classAnalysisCount (analyze stable) > zero
      extractOk =
        case extractBest nested stable (suc (enodeCount stable)) of λ where
          Nothing -> False
          (Just result) -> extractedCost result > zero
      quotientOk = classCount g5 < enodeCount g5
      iterationOk = saturationIterations report > zero
      saturationOk =
        saturationComplete report &&
        saturationComplete rightReport &&
        saturationComplete leftReport
  in egraphRegression
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
  regressionSaturationOk regressionGraph

symbolicEGraphRegression-proof :
  symbolicEGraphRegression ≡ True
symbolicEGraphRegression-proof = refl

eGraphAssociativityRegression : Bool
eGraphAssociativityRegression = regressionAssociativityOk regressionGraph

eGraphAssociativityRegression-proof :
  eGraphAssociativityRegression ≡ True
eGraphAssociativityRegression-proof = refl

eGraphAssociativityRegression : Bool
eGraphAssociativityRegression =
  case regressionGraph of λ where
    (_ , ok) -> ok

eGraphAssociativityRegression-proof :
  eGraphAssociativityRegression ≡ True
eGraphAssociativityRegression-proof = refl
