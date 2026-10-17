module FullCoupled.Agda2HsSemanticSearch where

open import Haskell.Prelude public

import FullCoupled.Agda2HsSemanticExtractor as Extractor
open import FullCoupled.Agda2HsTheoremGraphEGraph using
  ( symbolicEGraphRegression
  ; eGraphAssociativityRegression
  )

open import FullCoupled.Agda2HsTheoremGraphEGraph as EGraph

incrementSearchNat : Nat → Nat
incrementSearchNat n = n + 1

data Capability : Type where
  Inversion : Capability
  ExactSearch : Capability
  UniformContinuity : Capability

instance
  iEqCapability : Eq Capability
  iEqCapability ._==_ Inversion Inversion = True
  iEqCapability ._==_ ExactSearch ExactSearch = True
  iEqCapability ._==_ UniformContinuity UniformContinuity = True
  iEqCapability ._==_ _ _ = False

{-# COMPILE AGDA2HS iEqCapability #-}

-- A proposal prior is only a deterministic tie-break signal for the
-- capability planner. It is not an MDP action-value Q function.
record SemanticLaw : Type where
  no-eta-equality; pattern
  constructor MkSearchSemanticLaw
  field
    lawName : String
    capabilities : List Capability
    dependencies : List String
    proposalPrior : Nat

open SemanticLaw public

record SearchNode : Type where
  no-eta-equality; pattern
  constructor MkSearchNode
  field
    plan : List String
    covered : List Capability
    proposalScore : Nat

open SearchNode public

-- Search costs and fuel are Agda Nat values. The extracted Haskell
-- Prelude's length has type Int, so keep proof-search arithmetic explicit.
listLengthNat : {a : Type} -> List a -> Nat
listLengthNat [] = 0
listLengthNat (_ ∷ rest) = incrementSearchNat (listLengthNat rest)

requiredCapabilities : List Capability
requiredCapabilities =
  Inversion ∷ ExactSearch ∷ UniformContinuity ∷ []

capabilityCovered : Capability → List Capability → Bool
capabilityCovered c [] = False
capabilityCovered c (x ∷ xs) =
  if c == x then
    True
  else
    capabilityCovered c xs

addCapability : Capability → List Capability → List Capability
addCapability c cs =
  if capabilityCovered c cs then
    cs
  else
    c ∷ cs

-- Record every capability a law supplies on selection. Otherwise a law that
-- satisfies several requirements appears incomplete later, yet cannot be
-- selected again because its name already occurs in the plan.
addCapabilities : List Capability → List Capability → List Capability
addCapabilities [] covered = covered
addCapabilities (capability ∷ rest) covered =
  addCapabilities rest (addCapability capability covered)

allRequiredCovered : List Capability → List Capability → Bool
allRequiredCovered [] covered = True
allRequiredCovered (c ∷ cs) covered =
  if capabilityCovered c covered then
    allRequiredCovered cs covered
  else
    False

planContains : String → List String → Bool
planContains name [] = False
planContains name (x ∷ xs) =
  if name == x then
    True
  else
    planContains name xs

dependenciesSatisfied : List String → List String → Bool
dependenciesSatisfied [] plan = True
dependenciesSatisfied (dependency ∷ dependencies) plan =
  if planContains dependency plan then
    dependenciesSatisfied dependencies plan
  else
    False

coversLaw : Capability → SemanticLaw → Bool
coversLaw capability law =
  capabilityCovered capability (capabilities law)

firstMissing :
  List Capability →
  List Capability →
  Maybe Capability
firstMissing [] covered = Nothing
firstMissing (c ∷ cs) covered =
  if capabilityCovered c covered then
    firstMissing cs covered
  else
    Just c

expandForCapability :
  Capability →
  List SemanticLaw →
  SearchNode →
  List SearchNode
expandForCapability capability [] node = []
expandForCapability capability (law ∷ laws) node =
  let rest = expandForCapability capability laws node
  in
  if coversLaw capability law then
    if dependenciesSatisfied (dependencies law) (plan node) then
      if planContains (lawName law) (plan node) then
        rest
      else
        MkSearchNode
          (lawName law ∷ plan node)
          (addCapabilities (capabilities law) (covered node))
          (proposalScore node + proposalPrior law)
        ∷ rest
    else
      rest
  else
    rest
nodeCost : SearchNode → Nat
nodeCost node =
  listLengthNat (plan node)

-- Admissible one-step lower bound: any unfinished node needs at least one
-- more law insertion, while one law may satisfy several capabilities. Counting
-- missing capabilities would overestimate in that case and break A* optimality.
nodeHeuristic :
  List Capability →
  SearchNode →
  Nat
nodeHeuristic required node =
  if allRequiredCovered required (covered node) then 0 else incrementSearchNat 0

nodeHeuristicLowerBoundRegression : Bool
nodeHeuristicLowerBoundRegression =
  nodeHeuristic [] (MkSearchNode [] [] 0) == 0 &&
  nodeHeuristic (Inversion ∷ [])
    (MkSearchNode [] [] 0) == incrementSearchNat 0

nodeHeuristicLowerBoundRegressionChecked :
  nodeHeuristicLowerBoundRegression ≡ True
nodeHeuristicLowerBoundRegressionChecked = refl

nodeScore :
  List Capability →
  SearchNode →
  Nat
nodeScore required node =
  nodeCost node + nodeHeuristic required node

-- Larger accumulated proposal prior wins only when A* f scores tie.
higherProposalScore :
  SearchNode →
  SearchNode →
  Bool
higherProposalScore left right =
  proposalScore left >= proposalScore right

insertByScore :
  List Capability →
  SearchNode →
  List SearchNode →
  List SearchNode
insertByScore required node [] =
  node ∷ []
insertByScore required node (head ∷ tail) =
  if nodeScore required node < nodeScore required head then
    node ∷ head ∷ tail
  else
    if nodeScore required node == nodeScore required head then
      if higherProposalScore node head then
        node ∷ head ∷ tail
      else
        head ∷ insertByScore required node tail
    else
      head ∷ insertByScore required node tail

insertAll :
  List Capability →
  List SearchNode →
  List SearchNode →
  List SearchNode
insertAll required [] frontier = frontier
insertAll required (node ∷ nodes) frontier =
  insertAll
    required
    nodes
    (insertByScore required node frontier)

-- Repeat a payload once per list cell, keeping the depth parameter structural.
-- The generated Haskell list is lazy: its tail is produced only as A* consumes
-- fuel, rather than allocating the full factorial budget before search starts.
repeatBy : ∀ {a b : Type} → List a → List b → List b
repeatBy [] values = []
repeatBy (_ ∷ rest) values = values ++ repeatBy rest values

-- An input of length n produces n! unit cells, by the recurrence
-- (n+1)! = (n+1) * n!. Recursion follows the finite law list, not Nat.
factorialFuel : ∀ {a : Type} → List a → List ⊤
factorialFuel [] = tt ∷ []
factorialFuel (value ∷ rest) =
  repeatBy (value ∷ rest) (factorialFuel rest)

-- Four copies preserve the repository's bounded A* search contract.
searchFuel : List SemanticLaw → List ⊤
searchFuel laws =
  let fuel = factorialFuel laws
  in fuel ++ fuel ++ fuel ++ fuel

-- Consume one token per expanded frontier state. Exhaustion returns Nothing;
-- it is a resource bound, not proof that the dependency graph has no solution.
astarWithFuel :
  List ⊤ →
  List Capability →
  List SemanticLaw →
  List SearchNode →
  Maybe SearchNode
astarWithFuel [] required laws frontier = Nothing
astarWithFuel (_ ∷ fuel) required laws [] = Nothing
astarWithFuel (_ ∷ fuel) required laws (node ∷ frontier) =
  if allRequiredCovered required (covered node) then
    Just node
  else
    case firstMissing required (covered node) of λ where
      Nothing →
        Just node

      (Just capability) →
        let children = expandForCapability capability laws node
            frontier' = insertAll required children frontier
        in
        astarWithFuel fuel required laws frontier'

astar :
  List Capability →
  List SemanticLaw →
  List SearchNode →
  Maybe SearchNode
astar required laws frontier =
  astarWithFuel
    (searchFuel laws)
    required
    laws
    frontier

canonicalLaws : List SemanticLaw
canonicalLaws =
  MkSearchSemanticLaw
    "inverse-correct"
    (Inversion ∷ [])
    []
    (incrementSearchNat (incrementSearchNat (incrementSearchNat 0)))
  ∷ MkSearchSemanticLaw
      "inverse-csearchable"
      (ExactSearch ∷ [])
      ("inverse-correct" ∷ [])
      (incrementSearchNat (incrementSearchNat 0))
  ∷ MkSearchSemanticLaw
      "inverse-preserves-csearchability"
      (UniformContinuity ∷ [])
      ("inverse-csearchable" ∷ [])
      (incrementSearchNat 0)
  ∷ []

canonicalSearch : Maybe SearchNode
canonicalSearch =
  astar
    requiredCapabilities
    canonicalLaws
    (MkSearchNode [] [] 0 ∷ [])

canonicalPlan : List String
canonicalPlan =
  case canonicalSearch of λ where
    Nothing → []
    (Just node) → plan node

canonicalSearchComplete : Bool
canonicalSearchComplete =
  allRequiredCovered
    requiredCapabilities
    (case canonicalSearch of λ where
      Nothing → []
      (Just node) → covered node)

canonicalSearchIsComplete :
  canonicalSearchComplete ≡ True
canonicalSearchIsComplete = refl

-- One law may cover multiple outstanding requirements. The planner should use
-- that law once and record its entire contribution, not report a false miss.
multiCapabilityLaw : List SemanticLaw
multiCapabilityLaw =
  MkSearchSemanticLaw
    "combined-inverse-and-search"
    (Inversion ∷ ExactSearch ∷ [])
    []
    0
  ∷ []

multiCapabilitySearch : Maybe SearchNode
multiCapabilitySearch =
  astar
    (Inversion ∷ ExactSearch ∷ [])
    multiCapabilityLaw
    (MkSearchNode [] [] 0 ∷ [])

multiCapabilityCoverageRegression : Bool
multiCapabilityCoverageRegression =
  case multiCapabilitySearch of λ where
    Nothing → False
    (Just node) →
      allRequiredCovered
        (Inversion ∷ ExactSearch ∷ [])
        (covered node)
      && listLengthNat (plan node) == incrementSearchNat 0

multiCapabilityCoverageRegressionChecked :
  multiCapabilityCoverageRegression ≡ True
multiCapabilityCoverageRegressionChecked = refl

canonicalPlanNontrivial : Bool
canonicalPlanNontrivial =
  listLengthNat canonicalPlan == incrementSearchNat (incrementSearchNat (incrementSearchNat 0))

canonicalPlanIsNontrivial :
  canonicalPlanNontrivial ≡ True
canonicalPlanIsNontrivial = refl

pathAppend : List String → List String → List String
pathAppend [] ys = ys
pathAppend (x ∷ xs) ys = x ∷ pathAppend xs ys

splitTarget : List String
splitTarget =
  "inverse-correct" ∷ "inverse-csearchable" ∷ []

semanticSearchReport : String
semanticSearchReport =
  "ghc-agda2hs semantic search: "
  ++ show (length canonicalPlan)
  ++ " laws; target capabilities covered; A* cost is proof-independent guidance"

record GraphLaw : Type where
  no-eta-equality; pattern
  constructor MkGraphLaw
  field
    graphLawName : String
    graphLawDependencies : List String

open GraphLaw public

record GraphNode : Type where
  no-eta-equality; pattern
  constructor MkGraphNode
  field
    graphNodePlan : List String

open GraphNode public

graphLawForName :
  String -> List GraphLaw -> Maybe GraphLaw
graphLawForName _ [] = Nothing
graphLawForName name (law ∷ laws) =
  if name == (graphLawName law) then
    Just law
  else
    graphLawForName name laws

removeDuplicateStrings : List String -> List String -> List String
removeDuplicateStrings [] seen = seen
removeDuplicateStrings (x ∷ xs) seen =
  if planContains x seen then
    removeDuplicateStrings xs seen
  else
    removeDuplicateStrings xs (x ∷ seen)

graphLawAddDependency :
  String -> String -> List GraphLaw -> List GraphLaw
graphLawAddDependency name dependency [] =
  MkGraphLaw name (dependency ∷ []) ∷ []
graphLawAddDependency name dependency
  (law ∷ laws) =
  case name == graphLawName law of λ where
    True ->
      case planContains dependency (graphLawDependencies law) of λ where
        True -> MkGraphLaw name (graphLawDependencies law) ∷ laws
        False ->
          MkGraphLaw name
            (dependency ∷ graphLawDependencies law) ∷ laws
    False ->
      law ∷ graphLawAddDependency name dependency laws

ensureGraphLaw : String -> List GraphLaw -> List GraphLaw
ensureGraphLaw name [] = MkGraphLaw name [] ∷ []
ensureGraphLaw name (law ∷ laws) =
  if name == (graphLawName law) then
    law ∷ laws
  else
    law ∷ ensureGraphLaw name laws

graphLawsFromEdges :
  List (String × String) -> List GraphLaw
graphLawsFromEdges [] = []
graphLawsFromEdges ((source , target) ∷ edges) =
  graphLawAddDependency
    source
    target
    (ensureGraphLaw target (graphLawsFromEdges edges))

graphLawSeeds : List GraphLaw -> List GraphNode
graphLawSeeds [] = []
graphLawSeeds (law ∷ laws) =
  MkGraphNode (graphLawName law ∷ [])
  ∷ graphLawSeeds laws

graphContains : String -> List String -> Bool
graphContains = planContains

graphExpandDependencies :
  List String ->
  List String ->
  List GraphNode ->
  List GraphNode
graphExpandDependencies [] _ acc = reverse acc
graphExpandDependencies (dependency ∷ dependencies) plan acc =
  if graphContains dependency plan then
    graphExpandDependencies dependencies plan acc
  else
    -- Siblings branch from identical parent path. Do not carry dependency
    -- into the recursive plan; that would invent an edge between siblings.
    graphExpandDependencies
      dependencies
      plan
      (MkGraphNode (dependency ∷ plan) ∷ acc)

graphExpandNode :
  GraphNode -> List GraphLaw -> List GraphNode
graphExpandNode (MkGraphNode []) _ = []
graphExpandNode (MkGraphNode (terminal ∷ rest)) laws =
  case graphLawForName terminal laws of λ where
    Nothing -> []
    (Just law) ->
      graphExpandDependencies
        (graphLawDependencies law)
        (terminal ∷ rest)
        []

graphNodeScore : GraphNode -> Nat
graphNodeScore node = listLengthNat (graphNodePlan node)

graphInsert :
  GraphNode -> List GraphNode -> List GraphNode
graphInsert node [] = node ∷ []
graphInsert node (head ∷ tail) =
  if graphNodeScore node < graphNodeScore head then
    node ∷ head ∷ tail
  else
    head ∷ graphInsert node tail

graphInsertAll :
  List GraphNode -> List GraphNode -> List GraphNode
graphInsertAll [] frontier = frontier
graphInsertAll (node ∷ nodes) frontier =
  graphInsertAll nodes (graphInsert node frontier)

graphEdgeValid : String -> String -> List GraphLaw -> Bool
graphEdgeValid child parent laws =
  case graphLawForName parent laws of λ where
    Nothing -> False
    (Just law) ->
      planContains child (graphLawDependencies law)

graphValidChain :
  List String -> List GraphLaw -> Bool
graphValidChain [] _ = False
graphValidChain (_ ∷ []) _ = True
graphValidChain (child ∷ parent ∷ rest) laws =
  graphEdgeValid child parent laws &&
  graphValidChain (parent ∷ rest) laws

graphAllUnique :
  List String -> Bool
graphAllUnique [] = True
graphAllUnique (x ∷ xs) =
  if planContains x xs then
    False
  else
    graphAllUnique xs

graphValidPlan :
  List String -> List GraphLaw -> Bool
graphValidPlan [] _ = False
graphValidPlan plan laws =
  graphAllUnique plan && graphValidChain plan laws

-- Plans are stored deepest dependency first; the active node is the head.
graphFirst :
  List String ->
  Maybe String
graphFirst [] = Nothing
graphFirst (name ∷ _) = Just name

graphDependenciesCovered : List String -> List String -> Bool
graphDependenciesCovered [] _ = True
graphDependenciesCovered (dependency ∷ dependencies) plan =
  if graphContains dependency plan then
    graphDependenciesCovered dependencies plan
  else
    False

graphPlanHeadIsLeaf :
  List String ->
  List GraphLaw ->
  Bool
graphPlanHeadIsLeaf plan laws =
  case graphFirst plan of λ where
    Nothing -> False
    (Just terminal) ->
      case graphLawForName terminal laws of λ where
        Nothing -> False
        (Just law) ->
          graphLawDependencies law == []

graphMaximalDependencyChain :
  List String ->
  List GraphLaw ->
  Bool
graphMaximalDependencyChain plan laws =
  graphValidPlan plan laws && graphPlanHeadIsLeaf plan laws

graphAppend : {a : Type} -> List a -> List a -> List a
graphAppend [] ys = ys
graphAppend (x ∷ xs) ys = x ∷ graphAppend xs ys

graphConcatMap :
  {a b : Type} ->
  (a -> List b) ->
  List a ->
  List b
graphConcatMap _ [] = []
graphConcatMap f (x ∷ xs) =
  graphAppend (f x) (graphConcatMap f xs)

-- One unit token per law bounds the legacy depth-first enumeration
-- without matching on Nat constructors in extracted Haskell.
graphDepthFuel : List GraphLaw -> List ⊤
graphDepthFuel [] = []
graphDepthFuel (_ ∷ laws) = tt ∷ graphDepthFuel laws

mutual
  graphSearchChildren :
    List ⊤ ->
    List GraphLaw ->
    List GraphNode ->
    List (List String)
  graphSearchChildren depth laws [] = []
  graphSearchChildren depth laws (node ∷ nodes) =
    graphAppend
      (graphSearchDepth depth laws node)
      (graphSearchChildren depth laws nodes)

  graphSearchDepth :
    List ⊤ ->
    List GraphLaw ->
    GraphNode ->
    List (List String)
  graphSearchDepth [] _ _ = []
  graphSearchDepth (_ ∷ depth) laws node =
    if graphMaximalDependencyChain (graphNodePlan node) laws then
      (graphNodePlan node) ∷ []
    else
      graphSearchChildren
        depth
        laws
        (graphExpandNode node laws)

graphSearchSeeds :
  List ⊤ ->
  List GraphLaw ->
  List GraphNode ->
  List (List String)
graphSearchSeeds depth laws [] = []
graphSearchSeeds depth laws (node ∷ nodes) =
  graphAppend
    (graphSearchDepth depth laws node)
    (graphSearchSeeds depth laws nodes)

graphPlanScore : List String -> Nat
graphPlanScore = listLengthNat

graphInsertPlan :
  List String ->
  List (List String) ->
  List (List String)
graphInsertPlan plan [] = plan ∷ []
graphInsertPlan plan (head ∷ tail) =
  if graphPlanScore plan < graphPlanScore head then
    plan ∷ head ∷ tail
  else
    head ∷ graphInsertPlan plan tail

graphSortPlans :
  List (List String) ->
  List (List String)
graphSortPlans [] = []
graphSortPlans (plan ∷ plans) =
  graphInsertPlan plan (graphSortPlans plans)

autonomousGraphSearch :
  List (String × String) ->
  List (List String)
autonomousGraphSearch edges =
  let laws = graphLawsFromEdges edges
      seeds = graphLawSeeds laws
      candidates =
        graphSearchSeeds
          (graphDepthFuel laws)
          laws
          seeds
  in
  graphSortPlans candidates

autonomousGraphSearchCount :
  List (String × String) ->
  Nat
autonomousGraphSearchCount edges =
  listLengthNat (autonomousGraphSearch edges)

autonomousGraphSearchReport :
  List (String × String) ->
  String
autonomousGraphSearchReport edges =
  "agda2hs autonomous theorem-graph DFS: "
  ++ show (autonomousGraphSearchCount edges)
  ++ " maximal dependency chains"

stripDotPrefix : String -> String
stripDotPrefix ('"' ∷ rest) = stripDotPrefix rest
stripDotPrefix text = text

stripDotSuffixRev : String -> String
stripDotSuffixRev [] = []
stripDotSuffixRev (';' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev ('"' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev (']' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev rest = rest

stripDotSuffix : String -> String
stripDotSuffix text =
  reverse (stripDotSuffixRev (reverse text))

stripDotToken : String -> String
stripDotToken text =
  stripDotSuffix (stripDotPrefix text)

parseDotLine : String -> List (String × String)
parseDotLine line =
  case words line of λ where
    (source ∷ separator ∷ target ∷ rest) ->
      case separator == "->" of λ where
        True -> (stripDotToken source , stripDotToken target) ∷ []
        False -> []
    _ -> []

parseDotEdges : String -> List (String × String)
parseDotEdges source =
  concatMap parseDotLine (lines source)

parseDotQuotedEdgeRegression : Bool
parseDotQuotedEdgeRegression =
  case parseDotLine "\"A.Module\" -> \"B.Module\";" of λ where
    ((source , target) ∷ []) ->
      source == "A.Module" && target == "B.Module"
    _ -> False

parseDotAttributeEdgeRegression : Bool
parseDotAttributeEdgeRegression =
  case parseDotLine "\"A\" -> \"B\" [style=solid];" of λ where
    ((source , target) ∷ []) ->
      source == "A" && target == "B"
    _ -> False

parseDotMalformedLineRegression : Bool
parseDotMalformedLineRegression =
  listLengthNat (parseDotLine "digraph theorem {") == 0
    && listLengthNat (parseDotLine "// no dependency edge") == 0

graphDotParserRegression : Bool
graphDotParserRegression =
  parseDotQuotedEdgeRegression
    && parseDotAttributeEdgeRegression
    && parseDotMalformedLineRegression

canonicalGraphRoot : String
canonicalGraphRoot = "FullCoupled.Agda2HsSemanticSearch"

autonomousGraphSearchFromRoot :
  String ->
  List (String × String) ->
  List (List String)
autonomousGraphSearchFromRoot root edges =
  let laws = ensureGraphLaw root (graphLawsFromEdges edges)
  in
  graphSortPlans
    (graphSearchDepth
      (graphDepthFuel laws)
      laws
      (MkGraphNode (root ∷ [])))

autonomousCanonicalGraphSearch :
  String ->
  List (List String)
autonomousCanonicalGraphSearch source =
  autonomousGraphSearchFromRoot canonicalGraphRoot (parseDotEdges source)

autonomousCanonicalGraphSearchCount :
  String ->
  Nat
autonomousCanonicalGraphSearchCount source =
  listLengthNat (autonomousCanonicalGraphSearch source)

autonomousCanonicalGraphReport : String -> String
autonomousCanonicalGraphReport source =
  let edges = parseDotEdges source
      plans = autonomousCanonicalGraphSearch source
  in
  "theorem-graph-edges="
    ++ show (length edges)
    ++ " autonomous-depth-first-chains="
    ++ show (length plans)


autonomousGraphSearchRegression : Bool
autonomousGraphSearchRegression =
  let
    edges =
      ("A" , "B") ∷
      ("B" , "C") ∷
      []
    laws = graphLawsFromEdges edges
    plans = autonomousGraphSearchFromRoot "A" edges
  in
  case plans of λ where
    [] -> False
    (plan ∷ _) -> graphValidPlan plan laws

semanticGraphLaw :
  Extractor.SemanticLaw ->
  GraphLaw
semanticGraphLaw law =
  MkGraphLaw
    (Extractor.semanticLawId law)
    (Extractor.semanticLawDependencies law)

semanticGraphLaws :
  List Extractor.SemanticLaw ->
  List GraphLaw
semanticGraphLaws [] = []
semanticGraphLaws (law ∷ laws) =
  semanticGraphLaw law ∷ semanticGraphLaws laws

semanticLawForName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe Extractor.SemanticLaw
semanticLawForName _ [] = Nothing
semanticLawForName requested (law ∷ laws) =
  if Extractor.semanticLawName law == requested then
    Just law
  else
    semanticLawForName requested laws

-- Case/separator normalization repairs registry display aliases only. It does
-- not invent semantic edges or equate different theorem statements.
normalizeIdentifierChar : Char -> String
normalizeIdentifierChar value =
  if value == 'A' then "a" else
  if value == 'B' then "b" else
  if value == 'C' then "c" else
  if value == 'D' then "d" else
  if value == 'E' then "e" else
  if value == 'F' then "f" else
  if value == 'G' then "g" else
  if value == 'H' then "h" else
  if value == 'I' then "i" else
  if value == 'J' then "j" else
  if value == 'K' then "k" else
  if value == 'L' then "l" else
  if value == 'M' then "m" else
  if value == 'N' then "n" else
  if value == 'O' then "o" else
  if value == 'P' then "p" else
  if value == 'Q' then "q" else
  if value == 'R' then "r" else
  if value == 'S' then "s" else
  if value == 'T' then "t" else
  if value == 'U' then "u" else
  if value == 'V' then "v" else
  if value == 'W' then "w" else
  if value == 'X' then "x" else
  if value == 'Y' then "y" else
  if value == 'Z' then "z" else
  if value == '-' || value == '_' then "" else value ∷ []

normalizeIdentifier : String -> String
normalizeIdentifier [] = ""
normalizeIdentifier (value ∷ rest) =
  normalizeIdentifierChar value ++ normalizeIdentifier rest

semanticLawForNormalizedName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe Extractor.SemanticLaw
semanticLawForNormalizedName requested [] = Nothing
semanticLawForNormalizedName requested (law ∷ laws) =
  if normalizeIdentifier (Extractor.semanticLawName law)
       == normalizeIdentifier requested then
    Just law
  else
    semanticLawForNormalizedName requested laws

semanticLawForRequiredName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe Extractor.SemanticLaw
semanticLawForRequiredName requested laws =
  case semanticLawForName requested laws of λ where
    (Just law) -> Just law
    Nothing -> semanticLawForNormalizedName requested laws

semanticIdentifierNormalizationRegression : Bool
semanticIdentifierNormalizationRegression =
  normalizeIdentifier "CanonicalAQLoopTheorem"
    == normalizeIdentifier "canonical-aq-loop-theorem"

semanticIdentifierNormalizationRegressionChecked :
  semanticIdentifierNormalizationRegression ≡ True
semanticIdentifierNormalizationRegressionChecked = refl

-- A* state keeps the current law path and its explicit path cost g.
-- The exhaustive DFS above remains separate and continues to enumerate every
-- maximal dependency chain.
record GraphAStarNode : Type where
  no-eta-equality; pattern
  constructor MkGraphAStarNode
  field
    graphAStarPlan : List String
    graphAStarPathCost : Nat

open GraphAStarNode public

record GraphAStarBestCost : Type where
  no-eta-equality; pattern
  constructor MkGraphAStarBest
  field
    graphAStarBestName : String
    graphAStarBestG : Nat

open GraphAStarBestCost public

graphAStarKnownCost :
  String -> List GraphAStarBestCost -> Maybe Nat
graphAStarKnownCost _ [] = Nothing
graphAStarKnownCost requested (known ∷ remaining) =
  if requested == graphAStarBestName known then
    Just (graphAStarBestG known)
  else
    graphAStarKnownCost requested remaining

graphAStarRememberCost :
  String -> Nat -> List GraphAStarBestCost -> List GraphAStarBestCost
graphAStarRememberCost name cost [] =
  MkGraphAStarBest name cost ∷ []
graphAStarRememberCost name cost (known ∷ remaining) =
  if name == graphAStarBestName known then
    MkGraphAStarBest name cost ∷ remaining
  else
    known ∷ graphAStarRememberCost name cost remaining

-- Like JAxtar's optimal_mask, enqueue only a strictly cheaper g score for a
-- state; equal- or higher-cost duplicate states are discarded.
graphAStarCanImprove :
  String -> Nat -> List GraphAStarBestCost -> Bool
graphAStarCanImprove name cost known =
  case graphAStarKnownCost name known of λ where
    Nothing -> True
    (Just best) -> cost < best

graphAStarBestGRegression : Bool
graphAStarBestGRegression =
  let known = MkGraphAStarBest "A" (incrementSearchNat (incrementSearchNat 0)) ∷ []
  in
  graphAStarCanImprove "A" (incrementSearchNat 0) known
    && not (graphAStarCanImprove "A" (incrementSearchNat (incrementSearchNat 0)) known)
    && not (graphAStarCanImprove "A" (incrementSearchNat (incrementSearchNat (incrementSearchNat 0))) known)

graphAStarBestGRegressionChecked :
  graphAStarBestGRegression ≡ True
graphAStarBestGRegressionChecked = refl

graphAStarHeuristic :
  List GraphLaw ->
  GraphNode ->
  Nat
graphAStarHeuristic laws node =
  case graphFirst (graphNodePlan node) of λ where
    Nothing -> 0
    (Just terminal) ->
      case graphLawForName terminal laws of λ where
        Nothing -> 0
        (Just law) ->
          if graphLawDependencies law == [] then
            0
          else
            incrementSearchNat 0

-- JAxtar's default cost_weight is 1 - 1e-6. For Nat costs, scale its
-- f = cost_weight * g + h by 1,000,000 to compare the equivalent integer
-- score 999999*g + 1000000*h without floating-point rounding.
graphAStarScore :
  List GraphLaw ->
  GraphAStarNode ->
  Nat
graphAStarScore laws node =
  graphAStarPathCost node * 999999
    + graphAStarHeuristic laws (MkGraphNode (graphAStarPlan node)) * 1000000

graphAStarInsert :
  List GraphLaw ->
  GraphAStarNode ->
  List GraphAStarNode ->
  List GraphAStarNode
graphAStarInsert laws node [] =
  node ∷ []
graphAStarInsert laws node (head ∷ tail) =
  if graphAStarScore laws node <= graphAStarScore laws head then
    node ∷ head ∷ tail
  else
    head ∷ graphAStarInsert laws node tail

graphAStarInsertAll :
  List GraphLaw ->
  List GraphAStarNode ->
  List GraphAStarNode ->
  List GraphAStarNode
graphAStarInsertAll laws [] frontier = frontier
graphAStarInsertAll laws (node ∷ nodes) frontier =
  graphAStarInsertAll
    laws
    nodes
    (graphAStarInsert laws node frontier)

graphAStarWrapChildren :
  Nat ->
  List GraphNode ->
  List GraphAStarNode
graphAStarWrapChildren cost [] = []
graphAStarWrapChildren cost (child ∷ children) =
  MkGraphAStarNode (graphNodePlan child) cost
    ∷ graphAStarWrapChildren cost children

graphAStarExpandNode :
  GraphAStarNode -> List GraphLaw -> List GraphAStarNode
graphAStarExpandNode node laws =
  graphAStarWrapChildren
    (incrementSearchNat (graphAStarPathCost node))
    (graphExpandNode (MkGraphNode (graphAStarPlan node)) laws)

-- The first component is the g-cost table; the second is the priority queue.
-- State IDs are law names, the keys used by the dependency graph.
graphAStarEnqueueImprovements :
  List GraphLaw ->
  List GraphAStarNode ->
  List GraphAStarBestCost ->
  List GraphAStarNode ->
  List GraphAStarBestCost × List GraphAStarNode
graphAStarEnqueueImprovements laws [] known frontier =
  known , frontier
graphAStarEnqueueImprovements laws (node ∷ nodes) known frontier =
  case graphFirst (graphAStarPlan node) of λ where
    Nothing ->
      graphAStarEnqueueImprovements laws nodes known frontier
    (Just name) ->
      if graphAStarCanImprove name (graphAStarPathCost node) known then
        graphAStarEnqueueImprovements
          laws
          nodes
          (graphAStarRememberCost name (graphAStarPathCost node) known)
          (graphAStarInsert laws node frontier)
      else
        graphAStarEnqueueImprovements laws nodes known frontier

graphAStarFirstWithFuel :
  List ⊤ ->
  List GraphLaw ->
  List GraphAStarNode ->
  List GraphAStarBestCost ->
  Maybe (List String)
graphAStarFirstWithFuel [] laws frontier known =
  Nothing
graphAStarFirstWithFuel (_ ∷ fuel) laws [] known =
  Nothing
graphAStarFirstWithFuel (_ ∷ fuel) laws (node ∷ frontier) known =
  case graphFirst (graphAStarPlan node) of λ where
    Nothing ->
      graphAStarFirstWithFuel fuel laws frontier known
    (Just current) ->
      case graphAStarKnownCost current known of λ where
        Nothing ->
          graphAStarFirstWithFuel fuel laws frontier known
        (Just bestG) ->
          case (graphAStarPathCost node == bestG) of λ where
            False ->
              -- Skip stale queue entries superseded by a cheaper g score.
              graphAStarFirstWithFuel fuel laws frontier known
            True ->
              case graphMaximalDependencyChain (graphAStarPlan node) laws of λ where
                True ->
                  Just (graphAStarPlan node)
                False ->
                  let (known' , frontier') =
                        graphAStarEnqueueImprovements
                          laws
                          (graphAStarExpandNode node laws)
                          known
                          frontier
                  in graphAStarFirstWithFuel fuel laws frontier' known'

-- Every queued path is simple. The lazy fuel list preserves the previous
-- operational budget of three copies of n! without Nat-pattern extraction.
-- Exhausting fuel returns Nothing; it is not by itself a no-path theorem.
graphAStarFuelBound : List GraphLaw -> List ⊤
graphAStarFuelBound laws =
  let fuel = factorialFuel laws
  in fuel ++ fuel ++ fuel

graphAStarFirst :
  List GraphLaw ->
  GraphNode ->
  Maybe (List String)
graphAStarFirst laws seed =
  case graphFirst (graphNodePlan seed) of λ where
    Nothing -> Nothing
    (Just root) ->
      let initialCost = graphNodeScore seed in
      graphAStarFirstWithFuel
        (graphAStarFuelBound laws)
        laws
        (MkGraphAStarNode (graphNodePlan seed) initialCost ∷ [])
        (MkGraphAStarBest root initialCost ∷ [])

graphAStarTieBreakRegression : Bool
graphAStarTieBreakRegression =
  let
    laws =
      MkGraphLaw "A" [] ∷
      MkGraphLaw "B" [] ∷
      []
    existing = MkGraphAStarNode ("A" ∷ []) 0
    incoming = MkGraphAStarNode ("B" ∷ []) 0
  in
  case graphAStarInsert laws incoming (existing ∷ []) of λ where
    (MkGraphAStarNode (firstName ∷ []) _ ∷
     MkGraphAStarNode (secondName ∷ []) _ ∷ []) ->
      firstName == "B" && secondName == "A"
    _ -> False

graphAStarTieBreakRegressionChecked :
  graphAStarTieBreakRegression ≡ True
graphAStarTieBreakRegressionChecked = refl

graphStringPathEqual : List String -> List String -> Bool
graphStringPathEqual [] [] = True
graphStringPathEqual (left ∷ lefts) (right ∷ rights) =
  left == right && graphStringPathEqual lefts rights
graphStringPathEqual _ _ = False

-- A* must prefer the direct leaf over a longer sibling branch. This checks
-- shortest-path semantics independently of the exhaustive branch enumerator.
graphAStarShortestPathRegression : Bool
graphAStarShortestPathRegression =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ "C" ∷ []) ∷
      MkGraphLaw "B" ("D" ∷ []) ∷
      MkGraphLaw "C" [] ∷
      MkGraphLaw "D" [] ∷
      []
  in
  case graphAStarFirst laws (MkGraphNode ("A" ∷ [])) of λ where
    Nothing -> False
    (Just selected) ->
      graphValidPlan selected laws
        && graphStringPathEqual selected ("C" ∷ "A" ∷ [])
        && listLengthNat selected == incrementSearchNat (incrementSearchNat 0)

graphAStarShortestPathRegressionChecked :
  graphAStarShortestPathRegression ≡ True
graphAStarShortestPathRegressionChecked = refl

graphPathMember : List String -> List (List String) -> Bool
graphPathMember _ [] = False
graphPathMember target (candidate ∷ candidates) =
  graphStringPathEqual target candidate || graphPathMember target candidates

graphNodePlanMember : List String -> List GraphNode -> Bool
graphNodePlanMember _ [] = False
graphNodePlanMember target (node ∷ nodes) =
  graphStringPathEqual target (graphNodePlan node) ||
  graphNodePlanMember target nodes

graphDependencyOrderRegression : Bool
graphDependencyOrderRegression =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ "C" ∷ []) ∷
      MkGraphLaw "B" [] ∷
      MkGraphLaw "C" [] ∷
      []
    nodes = graphExpandNode (MkGraphNode ("A" ∷ [])) laws
  in
  graphNodePlanMember ("B" ∷ "A" ∷ []) nodes &&
  graphNodePlanMember ("C" ∷ "A" ∷ []) nodes &&
  listLengthNat nodes == incrementSearchNat (incrementSearchNat 0)

graphDependencyOrderRegressionChecked :
  graphDependencyOrderRegression ≡ True
graphDependencyOrderRegressionChecked = refl

-- Regression: each outgoing dependency must expand from the same parent.
-- A branch must not inherit a sibling dependency and invent a path edge.
graphTwoLeafBranchesRegression : Bool
graphTwoLeafBranchesRegression =
  let
    edges =
      ("A" , "B") ∷
      ("A" , "C") ∷
      []
    plans = autonomousGraphSearchFromRoot "A" edges
  in
  graphPathMember ("B" ∷ "A" ∷ []) plans &&
  graphPathMember ("C" ∷ "A" ∷ []) plans &&
  listLengthNat plans == incrementSearchNat (incrementSearchNat 0)

graphTwoLeafBranchesRegressionChecked :
  graphTwoLeafBranchesRegression ≡ True
graphTwoLeafBranchesRegressionChecked = refl

graphCycleIsRejectedRegression : Bool
graphCycleIsRejectedRegression =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ []) ∷
      MkGraphLaw "B" ("A" ∷ []) ∷
      []
  in
  not (graphMaximalDependencyChain ("B" ∷ "A" ∷ []) laws)

graphCycleIsRejectedRegressionChecked :
  graphCycleIsRejectedRegression ≡ True
graphCycleIsRejectedRegressionChecked = refl

------------------------------------------------------------------------
-- Complete dependency closure is an AND-dependency problem, not a path.
-- Reachability gathers every predecessor; a bounded topological pass emits
-- dependencies before their users. Missing names and cycles return Nothing.
------------------------------------------------------------------------

-- Closure traversal queues dependency entries, not just distinct vertices.
-- Bound fuel by adjacency-list size as well as vertex count; repeated
-- dependency entries must not make a valid graph report exhaustion.
graphClosureDependencyFuel : List GraphLaw -> List ⊤
graphClosureDependencyFuel [] = []
graphClosureDependencyFuel (law ∷ laws) =
  repeatBy (graphLawDependencies law) (tt ∷ [])
    ++ graphClosureDependencyFuel laws

graphClosureFuel : List GraphLaw -> List ⊤
graphClosureFuel laws =
  graphDepthFuel laws ++ graphClosureDependencyFuel laws ++ (tt ∷ [])

graphReachableNames :
  List ⊤ ->
  List String ->
  List String ->
  List GraphLaw ->
  Maybe (List String)
graphReachableNames [] [] seen laws = Just seen
graphReachableNames [] (_ ∷ _) seen laws = Nothing
graphReachableNames (_ ∷ fuel) [] seen laws = Just seen
graphReachableNames (_ ∷ fuel) (name ∷ pending) seen laws =
  if graphContains name seen then
    graphReachableNames fuel pending seen laws
  else
    case graphLawForName name laws of λ where
      Nothing -> Nothing
      (Just law) ->
        graphReachableNames
          fuel
          (graphAppend (graphLawDependencies law) pending)
          (name ∷ seen)
          laws

graphRemoveName : String -> List String -> List String
graphRemoveName name [] = []
graphRemoveName name (candidate ∷ rest) =
  if name == candidate then
    rest
  else
    candidate ∷ graphRemoveName name rest

graphFindReady :
  List String ->
  List String ->
  List GraphLaw ->
  Maybe String
graphFindReady [] completed laws = Nothing
graphFindReady (name ∷ remaining) completed laws =
  case graphLawForName name laws of λ where
    Nothing -> Nothing
    (Just law) ->
      if graphDependenciesCovered (graphLawDependencies law) completed then
        Just name
      else
        graphFindReady remaining completed laws

graphTopologicalSort :
  List ⊤ ->
  List String ->
  List GraphLaw ->
  List String ->
  Maybe (List String)
graphTopologicalSort [] [] laws completed = Just completed
graphTopologicalSort [] (_ ∷ _) laws completed = Nothing
graphTopologicalSort (_ ∷ fuel) [] laws completed = Just completed
graphTopologicalSort (_ ∷ fuel) remaining laws completed =
  case graphFindReady remaining completed laws of λ where
    Nothing -> Nothing
    (Just ready) ->
      graphTopologicalSort
        fuel
        (graphRemoveName ready remaining)
        laws
        (graphAppend completed (ready ∷ []))

graphDependencyClosure :
  String ->
  List GraphLaw ->
  Maybe (List String)
graphDependencyClosure root laws =
  case graphReachableNames
    (graphClosureFuel laws)
    (root ∷ [])
    []
    laws of λ where
      Nothing -> Nothing
      (Just reachable) ->
        graphTopologicalSort
          (graphDepthFuel laws)
          reachable
          laws
          []

graphPrecedes : String -> String -> List String -> Bool
graphPrecedes target later [] = False
graphPrecedes target later (name ∷ rest) =
  if name == target then
    graphContains later rest
  else
    graphPrecedes target later rest

graphClosureDependenciesValid :
  List String ->
  String ->
  List String ->
  Bool
graphClosureDependenciesValid [] owner closure = True
graphClosureDependenciesValid (dependency ∷ rest) owner closure =
  graphContains dependency closure
    && graphPrecedes dependency owner closure
    && graphClosureDependenciesValid rest owner closure

graphClosureMemberValid :
  List GraphLaw ->
  List String ->
  String ->
  Bool
graphClosureMemberValid laws closure name =
  case graphLawForName name laws of λ where
    Nothing -> False
    (Just law) ->
      graphClosureDependenciesValid
        (graphLawDependencies law)
        name
        closure

graphClosureMembersValid :
  List String ->
  List GraphLaw ->
  List String ->
  Bool
graphClosureMembersValid [] laws closure = True
graphClosureMembersValid (name ∷ rest) laws closure =
  graphClosureMemberValid laws closure name
    && graphClosureMembersValid rest laws closure

graphDependencyClosureValid :
  List GraphLaw ->
  List String ->
  Bool
graphDependencyClosureValid laws [] = False
graphDependencyClosureValid laws closure =
  graphAllUnique closure
    && graphClosureMembersValid closure laws closure

graphDependencyClosureRegression : Bool
graphDependencyClosureRegression =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ "C" ∷ []) ∷
      MkGraphLaw "B" ("D" ∷ []) ∷
      MkGraphLaw "C" ("D" ∷ []) ∷
      MkGraphLaw "D" [] ∷
      []
  in
  case graphDependencyClosure "A" laws of λ where
    Nothing -> False
    (Just closure) ->
      graphDependencyClosureValid laws closure
        && graphContains "A" closure
        && graphContains "B" closure
        && graphContains "C" closure
        && graphContains "D" closure
        && listLengthNat closure == incrementSearchNat (incrementSearchNat (incrementSearchNat (incrementSearchNat 0)))

graphDependencyClosureRejectsCycleRegression : Bool
graphDependencyClosureRejectsCycleRegression =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ []) ∷
      MkGraphLaw "B" ("A" ∷ []) ∷
      []
  in
  case graphDependencyClosure "A" laws of λ where
    Nothing -> True
    (Just _) -> False

graphDependencyClosureRejectsMissingRegression : Bool
graphDependencyClosureRejectsMissingRegression =
  let laws = MkGraphLaw "A" ("Missing" ∷ []) ∷ [] in
  case graphDependencyClosure "A" laws of λ where
    Nothing -> True
    (Just _) -> False

-- Duplicate adjacency entries inflate the pending queue without adding new
-- vertices. The old vertex-count-only fuel exhausted before draining this
-- valid graph; edge-count fuel now covers the actual traversal work.
graphDependencyClosureRepeatedDependenciesRegression : Bool
graphDependencyClosureRepeatedDependenciesRegression =
  let
    repeated =
      "B" ∷ "B" ∷ "B" ∷ "B" ∷ "B" ∷ "B" ∷ "B" ∷ "B" ∷ []
    laws =
      MkGraphLaw "A" repeated ∷
      MkGraphLaw "B" [] ∷
      []
  in
  case graphDependencyClosure "A" laws of λ where
    Nothing -> False
    (Just closure) ->
      graphDependencyClosureValid laws closure
        && graphContains "A" closure
        && graphContains "B" closure
        && listLengthNat closure == incrementSearchNat (incrementSearchNat 0)

-- Duplicate input arrows must neither multiply a node's dependency list nor
-- produce duplicate sibling paths.
graphDuplicateEdgeSearchRegression : Bool
graphDuplicateEdgeSearchRegression =
  let
    edges =
      ("A" , "B") ∷
      ("A" , "B") ∷
      []
    laws = graphLawsFromEdges edges
    plans = autonomousGraphSearchFromRoot "A" edges
  in
  case graphLawForName "A" laws of λ where
    Nothing -> False
    (Just law) ->
      listLengthNat (graphLawDependencies law) == incrementSearchNat 0
        && listLengthNat plans == incrementSearchNat 0
        && graphPathMember ("B" ∷ "A" ∷ []) plans

-- A multi-parent diamond must preserve both valid dependency chains. A*
-- may return either equal-cost branch, never a fabricated sibling edge.
graphMultiParentSearchRegression : Bool
graphMultiParentSearchRegression =
  let
    edges =
      ("A" , "B") ∷
      ("A" , "C") ∷
      ("B" , "D") ∷
      ("C" , "D") ∷
      []
    laws = graphLawsFromEdges edges
    plans = autonomousGraphSearchFromRoot "A" edges
    astarValid =
      case graphAStarFirst laws (MkGraphNode ("A" ∷ [])) of λ where
        Nothing -> False
        (Just selected) ->
          graphValidPlan selected laws
            && listLengthNat selected == incrementSearchNat (incrementSearchNat (incrementSearchNat 0))
            && (graphStringPathEqual selected ("D" ∷ "B" ∷ "A" ∷ [])
              || graphStringPathEqual selected ("D" ∷ "C" ∷ "A" ∷ []))
  in
  graphPathMember ("D" ∷ "B" ∷ "A" ∷ []) plans
    && graphPathMember ("D" ∷ "C" ∷ "A" ∷ []) plans
    && listLengthNat plans == incrementSearchNat (incrementSearchNat 0)
    && astarValid

graphSelfLoopRejectedRegression : Bool
graphSelfLoopRejectedRegression =
  let
    edges = ("A" , "A") ∷ []
    laws = graphLawsFromEdges edges
    plans = autonomousGraphSearchFromRoot "A" edges
    astarRejects =
      case graphAStarFirst laws (MkGraphNode ("A" ∷ [])) of λ where
        Nothing -> True
        (Just _) -> False
  in
  listLengthNat plans == 0 && astarRejects

-- A focused obligation graph separate from the inverse/exact-search graph.
-- Each path is an explicit dependency chain, not itself a proof term.
learnerObligationGraph : List GraphLaw
learnerObligationGraph =
  graphLawsFromEdges
    (("canonicalLearnerTraceGuarded" , "canonicalLearnerTrace") ∷
     ("canonicalLearnerTrace" , "canonicalFullStep") ∷
     ("canonicalFullStep" , "canonicalOptimizerStep") ∷
     ("canonicalOptimizerStep" , "f4ThetaStep") ∷
     ("f4ThetaStep" , "optimizerQuadratic") ∷
     ("canonicalOptimizerDescentObligation" , "f4ThetaOneStepDescentObligation") ∷
     ("f4ThetaOneStepDescentObligation" , "optimizerQuadratic") ∷
     [])

-- These are dependency closures, not single root-to-leaf paths: every
-- transitive prerequisite must be present and ordered before its dependents.
learnerTracePlan : Maybe (List String)
learnerTracePlan =
  graphDependencyClosure "canonicalLearnerTraceGuarded" learnerObligationGraph

learnerDescentPlan : Maybe (List String)
learnerDescentPlan =
  graphDependencyClosure "canonicalOptimizerDescentObligation" learnerObligationGraph

learnerLogicalGraphRegression : Bool
learnerLogicalGraphRegression =
  case learnerTracePlan of λ where
    Nothing → False
    (Just tracePlan) →
      case learnerDescentPlan of λ where
        Nothing → False
        (Just descentPlan) →
          graphDependencyClosureValid learnerObligationGraph tracePlan
            && graphDependencyClosureValid learnerObligationGraph descentPlan
            && graphContains "canonicalLearnerTraceGuarded" tracePlan
            && graphContains "canonicalFullStep" tracePlan
            && graphContains "optimizerQuadratic" tracePlan
            && graphContains "canonicalOptimizerDescentObligation" descentPlan
            && graphContains "f4ThetaOneStepDescentObligation" descentPlan
            && graphContains "optimizerQuadratic" descentPlan

learnerLogicalGraphRegressionChecked :
  learnerLogicalGraphRegression ≡ True
learnerLogicalGraphRegressionChecked = refl


------------------------------------------------------------------------
-- Coverage/dependency graph for the learner's connected semantics.
-- These edges are search/verification obligations, not claims of theorem
-- entailment. Missing semantic bridges are named explicitly instead of being
-- silently promoted to established optimality results.
------------------------------------------------------------------------

learnerSemanticBridgeGraph : List GraphLaw
learnerSemanticBridgeGraph =
  graphLawsFromEdges
    (("LearnerSemanticCoverageSuite" , "canonicalLearnerTraceGuarded") ∷
     ("LearnerSemanticCoverageSuite" , "canonicalLearnerTraceScan") ∷
     ("LearnerSemanticCoverageSuite" , "canonicalLearnerTraceAt") ∷
     ("LearnerSemanticCoverageSuite" , "canonicalTotalCountAfter") ∷
     ("LearnerSemanticCoverageSuite" , "rewardDependentBetaOptimalityBridge-obligation") ∷
     ("LearnerSemanticCoverageSuite" , "ScottStracheyDomains.denote") ∷
     ("LearnerSemanticCoverageSuite" , "ScottStracheyDomains.denotationalCompositionalityRegression") ∷
     ("LearnerSemanticCoverageSuite" , "ScottStracheyDomains.denotationalBottomStrictnessRegression") ∷
     ("LearnerSemanticCoverageSuite" , "ScottStracheyDomains.scottErshovNLabDenotationalSemanticsRegression") ∷
     ("LearnerSemanticCoverageSuite" , "CanonicalLearnerDenotation.canonicalLearnerDenotationBottom") ∷
     ("LearnerSemanticCoverageSuite" , "CanonicalLearnerDenotation.canonicalLearnerTraceDenotationStep") ∷
     ("LearnerSemanticCoverageSuite" , "ConstructivistDomainRewriteSuite") ∷
     ("ConstructivistDomainRewriteSuite" , "EGraph.russianConstructivismPostulateRule") ∷
     ("ConstructivistDomainRewriteSuite" , "EGraph.scottErshovDenotationalSemanticsPostulateRule") ∷
     ("ConstructivistDomainRewriteSuite" , "EGraph.bishopConstructivismPostulateRule") ∷
     ("ConstructivistDomainRewriteSuite" , "EGraph.constructivistPostulateRegression") ∷
     ("EGraph.constructivistPostulateRegression" , "EGraph.semanticRewriteRules") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.associativityRule") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.emptyRightRule") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.emptyLeftRule") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.russianConstructivismPostulateRule") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.scottErshovDenotationalSemanticsPostulateRule") ∷
     ("EGraph.semanticRewriteRules" , "EGraph.bishopConstructivismPostulateRule") ∷
     ("CanonicalLearnerDenotation.canonicalLearnerTraceDenotationStep" , "CanonicalLearnerDenotation.liftedCanonicalFullStep") ∷
     ("CanonicalLearnerDenotation.liftedCanonicalFullStep" , "ScottStracheyDomains.liftStrictMap") ∷
     ("CanonicalLearnerDenotation.canonicalLearnerDenotationBottom" , "ScottStracheyDomains.liftStrictMapBottom") ∷
     ("LearnerSemanticCoverageSuite" , "LawvereDiagonal.noSurjectiveBooleanDiagonal") ∷
     ("LearnerSemanticCoverageSuite" , "OmegaKleeneFixedPoint.leastFixedPointIsFixed") ∷
     ("LearnerSemanticCoverageSuite" , "neuralBellmanInstantiation-obligation") ∷
     ("canonicalLearnerTraceGuarded" , "canonicalLearnerTrace") ∷
     ("canonicalLearnerTraceAt" , "canonicalLearnerTrace") ∷
     ("canonicalLearnerTraceAt" , "iterateCanonical") ∷
     ("canonicalLearnerTrace" , "canonicalLearnerTracePrefix") ∷
     ("canonicalTotalCountAfter" , "canonicalTotalCountStep") ∷
     ("canonicalTotalCountStep" , "canonicalCountStep") ∷
     ("canonicalCountStep" , "updateLCBCount") ∷
     ("ScottStracheyDomains.denotationalCompositionalityRegression" , "ScottStracheyDomains.denote") ∷
     ("ScottStracheyDomains.denotationalCompositionalityRegression" , "ScottStracheyDomains.strictNatAdd") ∷
     ("ScottStracheyDomains.denotationalBottomStrictnessRegression" , "ScottStracheyDomains.denote") ∷
     ("canonicalLearnerTrace" , "MonoidLSTMStreams.iterateStream") ∷
     ("canonicalLearnerTracePrefix" , "MonoidLSTMStreams.iterateStreamPrefix") ∷
     ("canonicalLearnerTracePrefix" , "canonicalFullStep") ∷
     ("MonoidLSTMStreams.iterateStreamPrefix" , "MonoidLSTMStreams.iterateStream") ∷
     ("MonoidLSTMStreams.iterateStreamPrefix" , "MonoidLSTMStreams.iterateList") ∷
     ("MonoidLSTMStreams.iterateStream" , "canonicalFullStep") ∷
     ("canonicalLearnerTraceScan" , "canonicalLearnerTrace") ∷
     ("canonicalLearnerTraceScan" , "scanLearnerStream") ∷
     ("scanLearnerStream" , "MonoidLSTMStreams.scanSeededStream") ∷
     ("MonoidLSTMStreams.scanSeededStream" , "MonoidLSTMStreams.Stream") ∷
     ("canonicalFullStep" , "canonicalWatkinsStep") ∷
     ("canonicalFullStep" , "canonicalGRUStep") ∷
     ("canonicalFullStep" , "canonicalOptimizerStep") ∷
     ("canonicalFullStep" , "canonicalCountStep") ∷
     ("canonicalFullStep" , "canonicalQLogControlStep") ∷
     ("canonicalFullStep" , "canonicalQLogStep") ∷
     ("canonicalFullStep" , "canonicalHaarAccumulatorStep") ∷
     ("canonicalWatkinsStep" , "canonicalSignal") ∷
     ("canonicalSignal" , "canonicalWatkinsTarget") ∷
     ("canonicalWatkinsTarget" , "canonicalReward8") ∷
     ("canonicalWatkinsTarget" , "canonicalQLogBias") ∷
     ("canonicalWatkinsTarget" , "maxCriticValue8") ∷
     ("canonicalWatkinsTarget" , "canonicalEndogenousFeedback") ∷
     ("canonicalEndogenousFeedback" , "canonicalGRUFeedback") ∷
     ("canonicalEndogenousFeedback" , "canonicalF4L2Feedback") ∷
     ("canonicalEndogenousFeedback" , "canonicalQLogControlFeedback") ∷
     ("canonicalEndogenousFeedback" , "canonicalQLogValueFeedback") ∷
     ("canonicalOptimizerStep" , "f4ThetaStep") ∷
     ("canonicalCountStep" , "updateLCBCount") ∷
     ("canonicalReward8" , "canonicalPolicyWeightCode") ∷
     ("canonicalPolicyWeightCode" , "canonicalPolicyWeight") ∷
     ("canonicalPolicyWeight" , "canonicalPolicy") ∷
     ("canonicalPolicy" , "sparsemaxPolicy") ∷
     ("canonicalPolicy" , "lcbScore") ∷
     ("rewardDependentBetaOptimalityBridge-obligation" , "canonicalPolicy") ∷
     ("rewardDependentBetaOptimalityBridge-obligation" , "canonicalReward8") ∷
     ("rewardDependentBetaOptimalityBridge-obligation" , "exactOptimalImpliesBetaOptimal") ∷
     ("rewardDependentBetaOptimalityBridge-obligation" , "noUniformBetaOptimalChoice") ∷
     ("rewardDependentBetaOptimalityBridge-obligation" , "canonicalPolicyExactMaximality-not-established") ∷
     ("exactOptimalImpliesBetaOptimal" , "ExactOptimalChoice.selectedMaximal") ∷
     ("exactOptimalImpliesBetaOptimal" , "leAddRight") ∷
     ("exactOptimalImpliesBetaOptimal" , "leTrans") ∷
     ("noUniformBetaOptimalChoice" , "counterReward") ∷
     ("noUniformBetaOptimalChoice" , "noSuccessorBoundedBySelf") ∷
     ("LawvereDiagonal.noSurjectiveBooleanDiagonal" , "LawvereDiagonal.lawvereFixedPoint") ∷
     ("LawvereDiagonal.noSurjectiveBooleanDiagonal" , "LawvereDiagonal.noBooleanFlipFixedPoint") ∷
     ("LawvereDiagonal.noBooleanFlipFixedPoint" , "LawvereDiagonal.booleanFlip") ∷
     ("ScottStracheyDomains.denote" , "ScottStracheyDomains.Lift") ∷
     ("ScottStracheyDomains.denote" , "ScottStracheyDomains.strictNatAdd") ∷
     ("ScottStracheyDomains.strictNatAdd" , "ScottStracheyDomains.bottom") ∷
     ("ScottStracheyDomains.strictNatAdd" , "ScottStracheyDomains.defined") ∷
     ("OmegaKleeneFixedPoint.leastFixedPointIsFixed" , "OmegaKleeneFixedPoint.leastFixedPoint") ∷
     ("OmegaKleeneFixedPoint.leastFixedPointIsFixed" , "OmegaContinuousEndomap.preservesOmegaSuprema") ∷
     ("OmegaKleeneFixedPoint.leastFixedPointIsFixed" , "OmegaKleeneFixedPoint.shiftedSupremum") ∷
     ("OmegaKleeneFixedPoint.shiftedSupremum" , "OmegaKleeneFixedPoint.iter") ∷
     ("OmegaKleeneFixedPoint.leastFixedPoint" , "OmegaKleeneFixedPoint.iter") ∷
     ("OmegaKleeneFixedPoint.leastFixedPoint" , "OmegaKleeneFixedPoint.iterChain") ∷
     ("OmegaKleeneFixedPoint.iterChain" , "OmegaContinuousEndomap.monotoneω") ∷
     ("neuralBellmanInstantiation-obligation" , "neuralBellmanOptimalValueIsFixed") ∷
     ("neuralBellmanInstantiation-obligation" , "neuralBellmanOptimalValueIsLeast") ∷
     ("neuralBellmanInstantiation-obligation" , "neuralBellmanValueIsSupremumOfQStar") ∷
     ("neuralBellmanInstantiation-obligation" , "neuralPolicyGreedyOptimalAtBellmanValue") ∷
     ("neuralBellmanInstantiation-obligation" , "exactQ-premise") ∷
     ("neuralBellmanInstantiation-obligation" , "learnerTransitionExpectationBridge-not-established") ∷
     ("neuralBellmanInstantiation-obligation" , "canonicalPolicy") ∷
     ("neuralBellmanInstantiation-obligation" , "canonicalWatkinsTarget") ∷
     ("neuralBellmanValueIsSupremumOfQStar" , "neuralBellmanOptimalValueIsFixed") ∷
     ("neuralBellmanValueIsSupremumOfQStar" , "NeuralPolicyMDP.mdpBellmanEquation") ∷
     ("neuralBellmanValueIsSupremumOfQStar" , "neuralBellmanQStar") ∷
     ("neuralBellmanQStar" , "neuralBellmanOptimalValueFunction") ∷
     ("neuralBellmanOptimalValueFunction" , "OmegaKleeneFixedPoint.leastFixedPoint") ∷
     ("neuralBellmanOptimalValueIsFixed" , "OmegaKleeneFixedPoint.leastFixedPointIsFixed") ∷
     ("neuralPolicyGreedyOptimalAtBellmanValue" , "exactQ-premise") ∷
     ("neuralPolicyGreedyOptimalAtBellmanValue" , "nnGreedy") ∷
     ("neuralPolicyGreedyOptimalAtBellmanValue" , "neuralBellmanQStar") ∷
     [])

learnerSemanticBridgePlan : Maybe (List String)
learnerSemanticBridgePlan =
  graphDependencyClosure "LearnerSemanticCoverageSuite" learnerSemanticBridgeGraph

learnerSemanticBridgeRegression : Bool
learnerSemanticBridgeRegression =
  case learnerSemanticBridgePlan of λ where
    Nothing → False
    (Just plan) →
      graphDependencyClosureValid learnerSemanticBridgeGraph plan
        && graphContains "canonicalLearnerTracePrefix" plan
        && graphContains "canonicalLearnerTraceAt" plan
        && graphContains "canonicalTotalCountAfter" plan
        && graphContains "ScottStracheyDomains.denotationalCompositionalityRegression" plan
        && graphContains "ScottStracheyDomains.denotationalBottomStrictnessRegression" plan
        && graphContains "ScottStracheyDomains.scottErshovNLabDenotationalSemanticsRegression" plan
        && graphContains "CanonicalLearnerDenotation.canonicalLearnerDenotationBottom" plan
        && graphContains "CanonicalLearnerDenotation.canonicalLearnerTraceDenotationStep" plan
        && graphContains "EGraph.constructivistPostulateRegression" plan
        && graphContains "EGraph.russianConstructivismPostulateRule" plan
        && graphContains "EGraph.scottErshovDenotationalSemanticsPostulateRule" plan
        && graphContains "EGraph.bishopConstructivismPostulateRule" plan
        && graphContains "MonoidLSTMStreams.iterateStreamPrefix" plan
        && graphContains "LawvereDiagonal.noSurjectiveBooleanDiagonal" plan
        && graphContains "canonicalWatkinsTarget" plan
        && graphContains "canonicalPolicy" plan
        && graphContains "exactOptimalImpliesBetaOptimal" plan
        && graphContains "noUniformBetaOptimalChoice" plan
        && graphContains "ScottStracheyDomains.denote" plan
        && graphContains "OmegaKleeneFixedPoint.leastFixedPointIsFixed" plan
        && graphContains "neuralBellmanValueIsSupremumOfQStar" plan
        && graphContains "neuralPolicyGreedyOptimalAtBellmanValue" plan
        && graphContains "exactQ-premise" plan
        && graphContains "canonicalPolicyExactMaximality-not-established" plan
        && graphContains "learnerTransitionExpectationBridge-not-established" plan

learnerSemanticBridgeRegressionChecked :
  learnerSemanticBridgeRegression ≡ True
learnerSemanticBridgeRegressionChecked = refl

learnerSemanticBridgeReport : String
learnerSemanticBridgeReport =
  "learner-semantic-bridge-closure=" ++ show learnerSemanticBridgeRegression


sourceOnlyLegacyRequiredNames : List String
sourceOnlyLegacyRequiredNames = "inverse-csearchable" ∷ []

requiredTheoremNames : List String
requiredTheoremNames =
  "CanonicalAQLoopTheorem" ∷
  "CanonicalFullLearnerConnectedScanConjugacyTheorem" ∷
  "S4PlusS5RecurrentScanTheorem" ∷
  "CanonicalQMunchausenL2SharedNegationPolarityTheorem" ∷
  "CanonicalExactCompositionTuringCompletenessContract" ∷
  "CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem" ∷
  "CanonicalPolymorphicSparsemaxCompositionTheorem" ∷
  "OffPolicyFunctionApproximationStabilityBoundary" ∷
  "canonicalLearnerBairdSevenStar" ∷
  "CanonicalExactRNNLMTheorem" ∷
  "CanonicalGlobalTokenLMCompositionTheorem" ∷
  "CanonicalIntegerHaarScaledOrthogonalityTheorem" ∷
  "NatRingSolverNormalizationTheorem" ∷
  "IntegerRingSolverNormalizationTheorem" ∷
  "ListMonoidSolverNormalizationTheorem" ∷
  "CanonicalAlgebraicTacticBackendTheorem" ∷
  "CanonicalSafeTacticNormalizationTheorem" ∷
  "CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem" ∷
  "AStarPlanMonoidTheorem" ∷
  "CanonicalTokenArbitraryLengthGenerationTheorem" ∷
  "CanonicalAStarCostGuidanceTheorem" ∷
  "CanonicalEndogenousEGraphAStarTransportClosureTheorem" ∷
  "CanonicalFiniteCycleExclusionIsomorphismTheorem" ∷
  "CanonicalOperatorCompositionTheorem" ∷
  "CanonicalLearnerPermutationCompositionImpossibilityTheorem" ∷
  "CanonicalHaarRecurrentCompositionTheorem" ∷
  "CanonicalFullCompositionGraphTheorem" ∷
  "CanonicalF4GlobalOptimizerStabilityTheorem" ∷
  "CanonicalPureNonOrangeBypassCompletionTheorem" ∷
  "ExactContractComputabilityBoundaryTheorem" ∷
  "StateIsomorphism" ∷
  "ExactTwoCounterConfiguration" ∷
  "ExactTwoCounterMachine" ∷
  "nashEveryFiniteGameViaBrouwer" ∷
  "brouwerMixedNashFixedPointBridge" ∷
  "finiteMixedNash-brouwer-egraph-astar-proof" ∷
  "finiteMixedNash-egraph-astar-convergence" ∷
  "finiteMixedNash-egraph-astar-eventualStationarity" ∷
  "finiteMixedNash-egraph-astar-proof" ∷
  "finiteMixedNash-cycle-transport" ∷
  "finiteMixedNash-from-GRU-tail" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed" ∷
  "canonicalFullLearner-no-finite-rank-stability" ∷
  "CanonicalHardSparsityDegeneracyTheorem" ∷
  "ActionWeights" ∷
  "actionSupportCount" ∷
  "actionWeightSum" ∷
  "actionWeightSquareSum" ∷
  "generalTsallis2Denominator" ∷
  "generalTsallis2Numerator" ∷
  "generalTsallis2NearDyadicSparsity" ∷
  "generalTsallis2NearDyadicSparsity-zero" ∷
  "generalTsallis2NearDyadicSparsity-definition" ∷
  "dyadicEquivalent" ∷
  "tsallis2NearDyadic-oneHot" ∷
  "generalSupportSparsityDyadic" ∷
  "generalSupportSparsityDyadic-definition" ∷
  []

requiredSubcompositionNames : List String
requiredSubcompositionNames =
  "CanonicalStationarySubcompositionTheorem" ∷ []

-- Legacy theorem inventory is source-scanned, not imported into this runtime.
runtimeRequiredNames : List String
runtimeRequiredNames =
  "graphDependencyOrderRegressionChecked" ∷
  "graphTwoLeafBranchesRegressionChecked" ∷
  "graphAStarTieBreakRegressionChecked" ∷
  "graphAStarBestGRegressionChecked" ∷
  "graphAStarShortestPathRegressionChecked" ∷
  "nodeHeuristicLowerBoundRegressionChecked" ∷
  "graphCycleIsRejectedRegressionChecked" ∷
  "learnerLogicalGraphRegressionChecked" ∷
  "learnerSemanticBridgeRegressionChecked" ∷
  "sourceOnlyLegacyBoundaryRegressionChecked" ∷
  "canonicalSearchPlanEGraphClosed" ∷
  "graphAStarPlanEGraphClosed" ∷
  []

requiredNames : List String
requiredNames = runtimeRequiredNames

-- Additional targets for the learner-specific graph.  The existing inverse,
-- exact-search, and required-theorem target lists remain unchanged.
learnerLogicalRequiredNames : List String
learnerLogicalRequiredNames =
  "canonicalOptimizerDescentObligation" ∷
  "canonicalLearnerTraceGuarded" ∷
  []

-- Reflexive top-level laws are still valid declarations and valid graph
-- roots. Only record fields are excluded as independent theorem targets.
semanticLawCanSeed : Extractor.SemanticLaw -> Bool
semanticLawCanSeed law =
  case Extractor.semanticLawKind law of λ where
    Extractor.SemanticRecordField → False
    Extractor.SemanticTopLevel → True

semanticLawSeedFilterRegression : Bool
semanticLawSeedFilterRegression =
  let
    topLevel =
      Extractor.MkSemanticLaw
        "Regression.agda" "top-level-law"
        False False "Set" []
        Extractor.SemanticTopLevel ""
    reflexive =
      Extractor.MkSemanticLaw
        "Regression.agda" "reflexive-law"
        True False "Set" []
        Extractor.SemanticTopLevel ""
    recordField =
      Extractor.MkSemanticLaw
        "Regression.agda" "record-field-law"
        False False "Set" []
        Extractor.SemanticRecordField "RegressionRecord"
  in
  semanticLawCanSeed topLevel
    && semanticLawCanSeed reflexive
    && not (semanticLawCanSeed recordField)

semanticLawSeedFilterRegressionChecked :
  semanticLawSeedFilterRegression ≡ True
semanticLawSeedFilterRegressionChecked = refl

requiredPlanForName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe (List String)
requiredPlanForName requested semanticLaws =
  case semanticLawForRequiredName requested semanticLaws of λ where
    Nothing -> Nothing
    (Just law) ->
      case semanticLawCanSeed law of λ where
        True ->
          graphDependencyClosure
            (Extractor.semanticLawId law)
            (semanticGraphLaws semanticLaws)
        False -> Nothing

-- Validate a complete dependency closure, not merely adjacent edges in one
-- path. Every direct prerequisite must occur earlier; duplicates are rejected.
requiredPlanIsValid :
  List Extractor.SemanticLaw ->
  List String ->
  Bool
requiredPlanIsValid semanticLaws plan =
  graphDependencyClosureValid (semanticGraphLaws semanticLaws) plan

requiredPlans :
  List String ->
  List Extractor.SemanticLaw ->
  List (String × List String)
requiredPlans [] _ = []
requiredPlans (name ∷ names) semanticLaws =
  case requiredPlanForName name semanticLaws of λ where
    Nothing ->
      requiredPlans names semanticLaws
    (Just plan) ->
      if requiredPlanIsValid semanticLaws plan then
        (name , plan) ∷ requiredPlans names semanticLaws
      else
        requiredPlans names semanticLaws

requiredPlanCount :
  List String ->
  List Extractor.SemanticLaw ->
  Nat
requiredPlanCount names semanticLaws =
  listLengthNat (requiredPlans names semanticLaws)

requiredPlanComplete :
  List String ->
  List Extractor.SemanticLaw ->
  Bool
requiredPlanComplete names semanticLaws =
  requiredPlanCount names semanticLaws == listLengthNat names

requiredPlanReport :
  List String ->
  List Extractor.SemanticLaw ->
  String
requiredPlanReport names semanticLaws =
  "required-plan-count="
    ++ show (requiredPlanCount names semanticLaws)
    ++ " required-plan-total="
    ++ show (length names)
    ++ " required-plan-regression="
    ++ show (requiredPlanComplete names semanticLaws)

requiredPlanFailureName :
  String ->
  List Extractor.SemanticLaw ->
  Bool
requiredPlanFailureName requested semanticLaws =
  case semanticLawForRequiredName requested semanticLaws of λ where
    Nothing -> True
    (Just law) ->
      case semanticLawCanSeed law of λ where
        False -> True
        True ->
          case graphDependencyClosure
            (Extractor.semanticLawId law)
            (semanticGraphLaws semanticLaws) of λ where
              Nothing -> True
              (Just plan) ->
                not (requiredPlanIsValid semanticLaws plan)

requiredPlanFailures :
  List String ->
  List Extractor.SemanticLaw ->
  List String
requiredPlanFailures [] semanticLaws = []
requiredPlanFailures (name ∷ names) semanticLaws =
  if requiredPlanFailureName name semanticLaws then
    name ∷ requiredPlanFailures names semanticLaws
  else
    requiredPlanFailures names semanticLaws

requiredPlanFailuresText : List String -> String
requiredPlanFailuresText [] = "none"
requiredPlanFailuresText (name ∷ []) = name
requiredPlanFailuresText (name ∷ names) =
  name ++ ", " ++ requiredPlanFailuresText names

requiredPlanFailureReport :
  List String ->
  List Extractor.SemanticLaw ->
  String
requiredPlanFailureReport names semanticLaws =
  "required-plan-failures="
    ++ requiredPlanFailuresText (requiredPlanFailures names semanticLaws)


learnerLogicalPlanReport :
  List Extractor.SemanticLaw ->
  String
learnerLogicalPlanReport _ =
  "learner-obligation-roots="
    ++ show (length learnerLogicalRequiredNames)
    ++ " learner-obligation-source-closure=not-claimed"
    ++ " learner-static-graph-regression="
    ++ show learnerLogicalGraphRegression

semanticLawExtractionReport :
  List Extractor.SemanticLaw ->
  String
semanticLawExtractionReport laws =
  "semantic-laws="
    ++ show (listLengthNat laws)
    ++ " nonreflexive="
    ++ show (Extractor.countNonreflexive laws)
    ++ " composite="
    ++ show (Extractor.countComposite laws)

semanticSearchExecutableReport :
  List Extractor.SemanticLaw ->
  String
semanticSearchExecutableReport laws =
  requiredPlanReport requiredNames laws
    ++ " egraph-regression="
    ++ show symbolicEGraphRegression
    ++ " egraph-associativity-regression="
    ++ show eGraphAssociativityRegression
    ++ " egraph-canonical-bindings="
    ++ show EGraph.canonicalBindingsRegression
    ++ " egraph-hashcons-after-union="
    ++ show EGraph.hashconsAfterUnionRegression
    ++ " egraph-constructivist-postulates="
    ++ show EGraph.constructivistPostulateRegression

stringListEqual : List String -> List String -> Bool
stringListEqual [] [] = True
stringListEqual [] (_ ∷ _) = False
stringListEqual (_ ∷ _) [] = False
stringListEqual (x ∷ xs) (y ∷ ys) =
  if x == y then
    stringListEqual xs ys
  else
    False

normalizedSignatureEqual : String -> String -> Bool
normalizedSignatureEqual left right =
  stringListEqual (words left) (words right)

semanticLawIsRecordField :
  Extractor.SemanticLaw ->
  Bool
semanticLawIsRecordField law =
  case Extractor.semanticLawKind law of λ where
    Extractor.SemanticRecordField -> True
    Extractor.SemanticTopLevel -> False

semanticLawIsReflexive :
  Extractor.SemanticLaw ->
  Bool
semanticLawIsReflexive law =
  Extractor.lawReflexive law

semanticLawNamePresent :
  String ->
  List Extractor.SemanticLaw ->
  Bool
semanticLawNamePresent name [] = False
semanticLawNamePresent name (law ∷ laws) =
  if Extractor.semanticLawName law == name then
    True
  else
    semanticLawNamePresent name laws

record DominanceEdge : Type where
  no-eta-equality; pattern
  constructor MkDominanceEdge
  field
    dominanceContainer : String
    dominanceTheorem : String
    dominanceField : String

open DominanceEdge public

-- Heuristic only: the scanner compares normalized source signature text
-- and verifies that the named record container exists. Equal text is evidence
-- for a review candidate, not a proof of logical implication or subsumption.
recordFieldSignatureCandidate :
  Extractor.SemanticLaw ->
  Extractor.SemanticLaw ->
  List Extractor.SemanticLaw ->
  Bool
recordFieldSignatureCandidate theorem fieldLaw knownLaws =
  if semanticLawIsRecordField theorem then
    False
  else if semanticLawIsRecordField fieldLaw then
    if semanticLawIsReflexive theorem then
      False
    else if normalizedSignatureEqual
      (Extractor.semanticLawSignature theorem)
      (Extractor.semanticLawSignature fieldLaw) then
      if Extractor.semanticLawContainer fieldLaw == "" then
        False
      else
        semanticLawNamePresent
          (Extractor.semanticLawContainer fieldLaw)
          knownLaws
    else
      False
  else
    False

signatureCandidateEdgeFor :
  Extractor.SemanticLaw ->
  Extractor.SemanticLaw ->
  List Extractor.SemanticLaw ->
  Maybe DominanceEdge
signatureCandidateEdgeFor theorem fieldLaw knownLaws =
  if recordFieldSignatureCandidate theorem fieldLaw knownLaws then
    Just
      (MkDominanceEdge
        (Extractor.semanticLawContainer fieldLaw)
        (Extractor.semanticLawName theorem)
        (Extractor.semanticLawName fieldLaw))
  else
    Nothing

signatureCandidateEdgesForFields :
  Extractor.SemanticLaw ->
  List Extractor.SemanticLaw ->
  List Extractor.SemanticLaw ->
  List DominanceEdge
signatureCandidateEdgesForFields theorem _ [] = []
signatureCandidateEdgesForFields theorem knownLaws (fieldLaw ∷ remainingFields) =
  case signatureCandidateEdgeFor theorem fieldLaw knownLaws of λ where
    Nothing ->
      signatureCandidateEdgesForFields theorem knownLaws remainingFields
    (Just edge) ->
      edge ∷ signatureCandidateEdgesForFields theorem knownLaws remainingFields

signatureCandidateEdgesForTheorems :
  List Extractor.SemanticLaw ->
  List Extractor.SemanticLaw ->
  List DominanceEdge
signatureCandidateEdgesForTheorems _ [] = []
signatureCandidateEdgesForTheorems knownLaws (law ∷ remainingLaws) =
  signatureCandidateEdgesForFields law knownLaws knownLaws
  ++ signatureCandidateEdgesForTheorems knownLaws remainingLaws

dominanceEdgeEqual :
  DominanceEdge ->
  DominanceEdge ->
  Bool
dominanceEdgeEqual left right =
  dominanceContainer left == dominanceContainer right
  &&
  dominanceTheorem left == dominanceTheorem right
  &&
  dominanceField left == dominanceField right

dominanceEdgeMember :
  DominanceEdge ->
  List DominanceEdge ->
  Bool
dominanceEdgeMember _ [] = False
dominanceEdgeMember edge (candidate ∷ rest) =
  if dominanceEdgeEqual edge candidate then
    True
  else
    dominanceEdgeMember edge rest

dedupeSignatureCandidateEdges :
  List DominanceEdge ->
  List DominanceEdge ->
  List DominanceEdge
dedupeSignatureCandidateEdges [] seen = reverse seen
dedupeSignatureCandidateEdges (edge ∷ edges) seen =
  if dominanceEdgeMember edge seen then
    dedupeSignatureCandidateEdges edges seen
  else
    dedupeSignatureCandidateEdges edges (edge ∷ seen)

graphSignatureCandidateEdges :
  List Extractor.SemanticLaw ->
  List DominanceEdge
graphSignatureCandidateEdges laws =
  dedupeSignatureCandidateEdges
    (signatureCandidateEdgesForTheorems laws laws)
    []

dedupeStringsWithSeen :
  List String ->
  List String ->
  List String
dedupeStringsWithSeen [] seen = reverse seen
dedupeStringsWithSeen (value ∷ values) seen =
  if planContains value seen then
    dedupeStringsWithSeen values seen
  else
    dedupeStringsWithSeen values (value ∷ seen)

dedupeStrings :
  List String ->
  List String
dedupeStrings values = dedupeStringsWithSeen values []

signatureMatchedTheoremCandidates :
  List Extractor.SemanticLaw ->
  List String
signatureMatchedTheoremCandidates laws =
  dedupeStrings
    (map dominanceTheorem (graphSignatureCandidateEdges laws))

knownRedundancyCandidateNames : List String
knownRedundancyCandidateNames =
  "integerLayerNorm-egraph-astar-eventual-semantic-closure" ∷
  "integerLayerNorm-egraph-astar-infinite-stable-tail" ∷
  "eGraphEconomicFixedPoint" ∷
  "eGraphEconomicWalrasianEquilibrium" ∷
  "eGraphEconomicComposition-injective" ∷
  []

allNamesPresent :
  List String ->
  List String ->
  Bool
allNamesPresent [] _ = True
allNamesPresent (name ∷ names) candidates =
  if planContains name candidates then
    allNamesPresent names candidates
  else
    False

knownRedundancyCandidatesPresent :
  List Extractor.SemanticLaw ->
  List String
knownRedundancyCandidatesPresent laws =
  let dominated = signatureMatchedTheoremCandidates laws
  in
  if allNamesPresent knownRedundancyCandidateNames dominated then
    knownRedundancyCandidateNames
  else
    []

semanticPlanEGraphReport :
  List String ->
  EGraph.SaturationReport
semanticPlanEGraphReport plan =
  let
    (_ , graph0) =
      EGraph.addExpr
        (EGraph.leftAssocExpr plan)
        EGraph.emptyGraph
    (_ , report) =
      EGraph.saturateUntilStable
        EGraph.semanticRewriteRules
        graph0
  in
  report

semanticPlanEGraphComplete :
  List String ->
  Bool
semanticPlanEGraphComplete plan =
  EGraph.saturationComplete
    (semanticPlanEGraphReport plan)

semanticPlanEGraphExtractable :
  List String ->
  Bool
semanticPlanEGraphExtractable plan =
  let
    (rootId , graph0) =
      EGraph.addExpr
        (EGraph.leftAssocExpr plan)
        EGraph.emptyGraph
    (graph , _) =
      EGraph.saturateUntilStable
        EGraph.semanticRewriteRules
        graph0
  in
  case
    EGraph.extractBest
      rootId
      graph
      (EGraph.extractFuelFor graph)
  of λ where
    Nothing -> False
    (Just bestResult) ->
      EGraph.extractedCost bestResult > 0

-- End-to-end bridge: run the semantic-law A* planner, saturate its selected
-- plan in the symbolic e-graph, and require a stable graph plus a costed
-- extraction. This checks pipeline connectivity, not proof validity of names.
canonicalSearchPlanEGraphSaturates : Bool
canonicalSearchPlanEGraphSaturates =
  case canonicalSearch of λ where
    Nothing -> False
    (Just node) -> semanticPlanEGraphComplete (plan node)

canonicalSearchPlanEGraphExtracts : Bool
canonicalSearchPlanEGraphExtracts =
  case canonicalSearch of λ where
    Nothing -> False
    (Just node) -> semanticPlanEGraphExtractable (plan node)

canonicalSearchPlanEGraphClosed : Bool
canonicalSearchPlanEGraphClosed =
  canonicalSearchComplete &&
  canonicalSearchPlanEGraphSaturates &&
  canonicalSearchPlanEGraphExtracts

canonicalSearchPlanEGraphSaturatesChecked :
  canonicalSearchPlanEGraphSaturates ≡ True
canonicalSearchPlanEGraphSaturatesChecked = refl

canonicalSearchPlanEGraphExtractsChecked :
  canonicalSearchPlanEGraphExtracts ≡ True
canonicalSearchPlanEGraphExtractsChecked = refl

canonicalSearchPlanEGraphClosedChecked :
  canonicalSearchPlanEGraphClosed ≡ True
canonicalSearchPlanEGraphClosedChecked = refl

-- A separate regression covers JAxtar-style dependency A*, not only the
-- capability planner: select a maximal leaf and pass that selected path
-- through the same e-graph saturation and costed extraction boundary.
graphAStarPlanEGraphClosed : Bool
graphAStarPlanEGraphClosed =
  let
    laws =
      MkGraphLaw "A" ("B" ∷ "C" ∷ []) ∷
      MkGraphLaw "B" ("D" ∷ []) ∷
      MkGraphLaw "C" [] ∷
      MkGraphLaw "D" [] ∷
      []
    seed = MkGraphNode ("A" ∷ [])
  in
  case graphAStarFirst laws seed of λ where
    Nothing -> False
    (Just selectedPlan) ->
      graphValidPlan selectedPlan laws
        && graphAStarShortestPathRegression
        && semanticPlanEGraphComplete selectedPlan
        && semanticPlanEGraphExtractable selectedPlan

graphAStarPlanEGraphClosedChecked :
  graphAStarPlanEGraphClosed ≡ True
graphAStarPlanEGraphClosedChecked = refl

plansEGraphClosed :
  List (List String) ->
  Bool
plansEGraphClosed [] = True
plansEGraphClosed (plan ∷ plans) =
  if semanticPlanEGraphComplete plan &&
     semanticPlanEGraphExtractable plan then
    plansEGraphClosed plans
  else
    False

requiredPlanEGraphCount :
  List String ->
  List Extractor.SemanticLaw ->
  Nat
requiredPlanEGraphCount [] _ = 0
requiredPlanEGraphCount (name ∷ names) laws =
  case requiredPlanForName name laws of λ where
    Nothing ->
      requiredPlanEGraphCount names laws
    (Just plan) ->
      let tail = requiredPlanEGraphCount names laws in
      if semanticPlanEGraphComplete plan &&
         semanticPlanEGraphExtractable plan then
        incrementSearchNat tail
      else
        tail

requiredPlanEGraphComplete :
  List String ->
  List Extractor.SemanticLaw ->
  Bool
requiredPlanEGraphComplete names laws =
  requiredPlanEGraphCount names laws == listLengthNat names

haskellMinusOneTargetCapabilities : List Capability
haskellMinusOneTargetCapabilities =
  Inversion ∷ ExactSearch ∷ []

haskellMinusOneLaws : List SemanticLaw
haskellMinusOneLaws =
  MkSearchSemanticLaw
    "inverse-correct"
    (Inversion ∷ [])
    []
    (incrementSearchNat (incrementSearchNat (incrementSearchNat 0)))
  ∷ MkSearchSemanticLaw
      "inverse-csearchable"
      (ExactSearch ∷ [])
      ("inverse-correct" ∷ [])
      (incrementSearchNat (incrementSearchNat 0))
  ∷ []

haskellMinusOneAStar : Maybe SearchNode
haskellMinusOneAStar =
  astar
    haskellMinusOneTargetCapabilities
    haskellMinusOneLaws
    (MkSearchNode [] [] 0 ∷ [])

haskellMinusOneAStarPlan : List String
haskellMinusOneAStarPlan =
  case haskellMinusOneAStar of λ where
    Nothing → []
    (Just node) → plan node

haskellMinusOneAStarComplete : Bool
haskellMinusOneAStarComplete =
  allRequiredCovered
    haskellMinusOneTargetCapabilities
    (case haskellMinusOneAStar of λ where
      Nothing → []
      (Just node) → covered node)

haskellMinusOneAStarIsComplete :
  haskellMinusOneAStarComplete ≡ True
haskellMinusOneAStarIsComplete = refl

hybridInverseExactRealPlan : List String
hybridInverseExactRealPlan =
  haskellMinusOneAStarPlan
  ++ "inverse-preserves-csearchability" ∷ []

hybridInverseExactRealSearchReport : String
hybridInverseExactRealSearchReport =
  "haskell-minus-one-A*="
    ++ show (length haskellMinusOneAStarPlan)
    ++ " proof-backed laws; legacy monolith excluded from pure build"

sourceOnlyLegacyRequiredReport : String
sourceOnlyLegacyRequiredReport =
  "source-only-legacy-required=inverse-csearchable; runtime-exact-search-plan="
    ++ show haskellMinusOneAStarComplete

sourceOnlyLegacyBoundaryRegression : Bool
sourceOnlyLegacyBoundaryRegression =
  not (planContains "inverse-csearchable" requiredNames)
    && not (planContains "CanonicalAQLoopTheorem" requiredNames)
    && not (planContains "CanonicalFullLearnerConnectedScanConjugacyTheorem" requiredNames)
    && not (planContains "CanonicalStationarySubcompositionTheorem" requiredNames)
    && haskellMinusOneAStarComplete

sourceOnlyLegacyBoundaryRegressionChecked :
  sourceOnlyLegacyBoundaryRegression ≡ True
sourceOnlyLegacyBoundaryRegressionChecked = refl

agdaSemanticPortReport :
  List Extractor.SemanticLaw ->
  String
agdaSemanticPortReport laws =
  "agda2hs-semantic-port="
    ++ show (length (graphSignatureCandidateEdges laws))
    ++ " signature-candidate edges; "
    ++ show (length (knownRedundancyCandidatesPresent laws))
    ++ " known redundancy candidates; "
    ++ show (requiredPlanEGraphCount requiredNames laws)
    ++ "/"
    ++ show (length requiredNames)
    ++ " required plans e-graph-closed; learner-obligation-roots="
    ++ show (length learnerLogicalRequiredNames)
    ++ "; learner-static-graph="
    ++ show learnerLogicalGraphRegression

main : IO ⊤
main = do
  source <- readFile "build/agda2hs-semantic-search/semantic-search.dot"
  semanticLaws <-
    Extractor.readSemanticLaws
      "build/agda2hs-semantic-search/.semantic-source-files"
  putStrLn semanticSearchReport
  putStrLn (autonomousGraphSearchReport (parseDotEdges source))
  putStrLn (autonomousCanonicalGraphReport source)
  putStrLn ("autonomous-regression=" ++ show autonomousGraphSearchRegression)
  putStrLn ("graph-branch-regression=" ++ show graphDependencyOrderRegression)
  putStrLn ("graph-two-leaf-paths=" ++ show graphTwoLeafBranchesRegression)
  putStrLn ("graph-best-first-tie=" ++ show graphAStarTieBreakRegression)
  putStrLn ("graph-cycle-rejected=" ++ show graphCycleIsRejectedRegression)
  putStrLn ("canonical-plan=" ++ show canonicalPlan)
  putStrLn (semanticLawExtractionReport semanticLaws)
  putStrLn (requiredPlanReport requiredNames semanticLaws)
  putStrLn (requiredPlanFailureReport requiredNames semanticLaws)
  putStrLn (learnerLogicalPlanReport semanticLaws)
  putStrLn learnerSemanticBridgeReport
  putStrLn ("semantic-identifier-normalization=" ++ show semanticIdentifierNormalizationRegression)
  putStrLn (semanticSearchExecutableReport semanticLaws)
  putStrLn hybridInverseExactRealSearchReport
  putStrLn sourceOnlyLegacyRequiredReport
  putStrLn ("source-only-legacy-boundary=" ++ show sourceOnlyLegacyBoundaryRegression)
  putStrLn (agdaSemanticPortReport semanticLaws)
  putStrLn ("canonical-search-egraph-closed=" ++ show canonicalSearchPlanEGraphClosed)

{-# COMPILE AGDA2HS normalizeIdentifierChar #-}
{-# COMPILE AGDA2HS normalizeIdentifier #-}
{-# COMPILE AGDA2HS semanticLawForNormalizedName #-}
{-# COMPILE AGDA2HS semanticLawForRequiredName #-}
{-# COMPILE AGDA2HS semanticIdentifierNormalizationRegression #-}
{-# COMPILE AGDA2HS sourceOnlyLegacyRequiredReport #-}
{-# COMPILE AGDA2HS sourceOnlyLegacyBoundaryRegression #-}

{-# COMPILE AGDA2HS main #-}

{-# COMPILE AGDA2HS Capability #-}
{-# COMPILE AGDA2HS SemanticLaw #-}
{-# COMPILE AGDA2HS GraphLaw #-}
{-# COMPILE AGDA2HS GraphNode #-}
{-# COMPILE AGDA2HS autonomousGraphSearch #-}
{-# COMPILE AGDA2HS graphLawForName #-}
{-# COMPILE AGDA2HS graphLawAddDependency #-}
{-# COMPILE AGDA2HS ensureGraphLaw #-}
{-# COMPILE AGDA2HS graphLawsFromEdges #-}
{-# COMPILE AGDA2HS graphLawSeeds #-}
{-# COMPILE AGDA2HS graphContains #-}
{-# COMPILE AGDA2HS graphExpandDependencies #-}
{-# COMPILE AGDA2HS graphExpandNode #-}
{-# COMPILE AGDA2HS graphNodeScore #-}
{-# COMPILE AGDA2HS graphInsert #-}
{-# COMPILE AGDA2HS graphInsertAll #-}
{-# COMPILE AGDA2HS graphEdgeValid #-}
{-# COMPILE AGDA2HS graphValidChain #-}
{-# COMPILE AGDA2HS graphAllUnique #-}
{-# COMPILE AGDA2HS graphValidPlan #-}
{-# COMPILE AGDA2HS graphFirst #-}
{-# COMPILE AGDA2HS graphDependenciesCovered #-}
{-# COMPILE AGDA2HS graphPlanHeadIsLeaf #-}
{-# COMPILE AGDA2HS graphMaximalDependencyChain #-}
{-# COMPILE AGDA2HS graphAppend #-}
{-# COMPILE AGDA2HS graphConcatMap #-}
{-# COMPILE AGDA2HS graphDepthFuel #-}
{-# COMPILE AGDA2HS graphSearchChildren #-}
{-# COMPILE AGDA2HS graphSearchDepth #-}
{-# COMPILE AGDA2HS graphSearchSeeds #-}
{-# COMPILE AGDA2HS graphPlanScore #-}
{-# COMPILE AGDA2HS graphInsertPlan #-}
{-# COMPILE AGDA2HS graphSortPlans #-}
{-# COMPILE AGDA2HS autonomousGraphSearchRegression #-}
{-# COMPILE AGDA2HS graphDependencyOrderRegression #-}
{-# COMPILE AGDA2HS graphTwoLeafBranchesRegression #-}
{-# COMPILE AGDA2HS graphAStarTieBreakRegression #-}
{-# COMPILE AGDA2HS graphAStarShortestPathRegression #-}
{-# COMPILE AGDA2HS graphAStarBestGRegression #-}
{-# COMPILE AGDA2HS GraphAStarNode #-}
{-# COMPILE AGDA2HS GraphAStarBestCost #-}
{-# COMPILE AGDA2HS graphCycleIsRejectedRegression #-}
{-# COMPILE AGDA2HS graphClosureFuel #-}
{-# COMPILE AGDA2HS graphReachableNames #-}
{-# COMPILE AGDA2HS graphRemoveName #-}
{-# COMPILE AGDA2HS graphFindReady #-}
{-# COMPILE AGDA2HS graphTopologicalSort #-}
{-# COMPILE AGDA2HS graphDependencyClosure #-}
{-# COMPILE AGDA2HS graphPrecedes #-}
{-# COMPILE AGDA2HS graphClosureDependenciesValid #-}
{-# COMPILE AGDA2HS graphClosureMemberValid #-}
{-# COMPILE AGDA2HS graphClosureMembersValid #-}
{-# COMPILE AGDA2HS graphDependencyClosureValid #-}
{-# COMPILE AGDA2HS graphDependencyClosureRegression #-}
{-# COMPILE AGDA2HS graphDependencyClosureRejectsCycleRegression #-}
{-# COMPILE AGDA2HS graphDependencyClosureRejectsMissingRegression #-}
{-# COMPILE AGDA2HS graphClosureDependencyFuel #-}
{-# COMPILE AGDA2HS graphDependencyClosureRepeatedDependenciesRegression #-}
{-# COMPILE AGDA2HS graphDuplicateEdgeSearchRegression #-}
{-# COMPILE AGDA2HS graphMultiParentSearchRegression #-}
{-# COMPILE AGDA2HS graphSelfLoopRejectedRegression #-}
{-# COMPILE AGDA2HS parseDotQuotedEdgeRegression #-}
{-# COMPILE AGDA2HS parseDotAttributeEdgeRegression #-}
{-# COMPILE AGDA2HS parseDotMalformedLineRegression #-}
{-# COMPILE AGDA2HS graphDotParserRegression #-}
{-# COMPILE AGDA2HS graphStringPathEqual #-}
{-# COMPILE AGDA2HS graphPathMember #-}
{-# COMPILE AGDA2HS graphNodePlanMember #-}
{-# COMPILE AGDA2HS autonomousGraphSearchCount #-}
{-# COMPILE AGDA2HS autonomousGraphSearchReport #-}
{-# COMPILE AGDA2HS SearchNode #-}
{-# COMPILE AGDA2HS requiredCapabilities #-}
{-# COMPILE AGDA2HS repeatBy #-}
{-# COMPILE AGDA2HS factorialFuel #-}
{-# COMPILE AGDA2HS searchFuel #-}
{-# COMPILE AGDA2HS astarWithFuel #-}
{-# COMPILE AGDA2HS listLengthNat #-}
{-# COMPILE AGDA2HS incrementSearchNat #-}
{-# COMPILE AGDA2HS planContains #-}
{-# COMPILE AGDA2HS capabilityCovered #-}
{-# COMPILE AGDA2HS addCapability #-}
{-# COMPILE AGDA2HS allRequiredCovered #-}
{-# COMPILE AGDA2HS dependenciesSatisfied #-}
{-# COMPILE AGDA2HS coversLaw #-}
{-# COMPILE AGDA2HS firstMissing #-}
{-# COMPILE AGDA2HS expandForCapability #-}
{-# COMPILE AGDA2HS nodeCost #-}
{-# COMPILE AGDA2HS nodeHeuristic #-}
{-# COMPILE AGDA2HS nodeHeuristicLowerBoundRegression #-}
{-# COMPILE AGDA2HS nodeScore #-}
{-# COMPILE AGDA2HS higherProposalScore #-}
{-# COMPILE AGDA2HS insertByScore #-}
{-# COMPILE AGDA2HS insertAll #-}
{-# COMPILE AGDA2HS canonicalLaws #-}
{-# COMPILE AGDA2HS astar #-}
{-# COMPILE AGDA2HS canonicalSearch #-}
{-# COMPILE AGDA2HS canonicalPlan #-}
{-# COMPILE AGDA2HS canonicalSearchComplete #-}
{-# COMPILE AGDA2HS canonicalPlanNontrivial #-}
{-# COMPILE AGDA2HS pathAppend #-}
{-# COMPILE AGDA2HS splitTarget #-}
{-# COMPILE AGDA2HS semanticSearchReport #-}
{-# COMPILE AGDA2HS canonicalGraphRoot #-}
{-# COMPILE AGDA2HS parseDotEdges #-}
{-# COMPILE AGDA2HS stripDotPrefix #-}
{-# COMPILE AGDA2HS stripDotSuffixRev #-}
{-# COMPILE AGDA2HS stripDotSuffix #-}
{-# COMPILE AGDA2HS stripDotToken #-}
{-# COMPILE AGDA2HS parseDotLine #-}
{-# COMPILE AGDA2HS graphAStarKnownCost #-}
{-# COMPILE AGDA2HS graphAStarRememberCost #-}
{-# COMPILE AGDA2HS graphAStarCanImprove #-}
{-# COMPILE AGDA2HS graphAStarHeuristic #-}
{-# COMPILE AGDA2HS graphAStarScore #-}
{-# COMPILE AGDA2HS graphAStarInsert #-}
{-# COMPILE AGDA2HS graphAStarInsertAll #-}
{-# COMPILE AGDA2HS graphAStarWrapChildren #-}
{-# COMPILE AGDA2HS graphAStarExpandNode #-}
{-# COMPILE AGDA2HS graphAStarEnqueueImprovements #-}
{-# COMPILE AGDA2HS graphAStarFirst #-}
{-# COMPILE AGDA2HS graphAStarFuelBound #-}
{-# COMPILE AGDA2HS graphAStarFirstWithFuel #-}
{-# COMPILE AGDA2HS autonomousGraphSearchFromRoot #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphSearch #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphSearchCount #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphReport #-}
{-# COMPILE AGDA2HS semanticGraphLaw #-}
{-# COMPILE AGDA2HS semanticGraphLaws #-}
{-# COMPILE AGDA2HS semanticLawForName #-}
{-# COMPILE AGDA2HS semanticLawCanSeed #-}
{-# COMPILE AGDA2HS requiredTheoremNames #-}
{-# COMPILE AGDA2HS requiredSubcompositionNames #-}
{-# COMPILE AGDA2HS requiredNames #-}
{-# COMPILE AGDA2HS requiredPlanForName #-}
{-# COMPILE AGDA2HS requiredPlanIsValid #-}
{-# COMPILE AGDA2HS requiredPlans #-}
{-# COMPILE AGDA2HS requiredPlanCount #-}
{-# COMPILE AGDA2HS requiredPlanComplete #-}
{-# COMPILE AGDA2HS requiredPlanFailureName #-}
{-# COMPILE AGDA2HS requiredPlanFailures #-}
{-# COMPILE AGDA2HS requiredPlanFailuresText #-}
{-# COMPILE AGDA2HS requiredPlanFailureReport #-}
{-# COMPILE AGDA2HS requiredPlanReport #-}
{-# COMPILE AGDA2HS semanticLawExtractionReport #-}
{-# COMPILE AGDA2HS semanticSearchExecutableReport #-}
{-# COMPILE AGDA2HS learnerLogicalRequiredNames #-}
{-# COMPILE AGDA2HS learnerTracePlan #-}
{-# COMPILE AGDA2HS learnerObligationGraph #-}
{-# COMPILE AGDA2HS learnerDescentPlan #-}
{-# COMPILE AGDA2HS learnerLogicalGraphRegression #-}
{-# COMPILE AGDA2HS learnerLogicalPlanReport #-}
{-# COMPILE AGDA2HS semanticLawSeedFilterRegression #-}
{-# COMPILE AGDA2HS learnerSemanticBridgeGraph #-}
{-# COMPILE AGDA2HS learnerSemanticBridgePlan #-}
{-# COMPILE AGDA2HS learnerSemanticBridgeRegression #-}
{-# COMPILE AGDA2HS learnerSemanticBridgeReport #-}
{-# COMPILE AGDA2HS DominanceEdge #-}
{-# COMPILE AGDA2HS graphSignatureCandidateEdges #-}
{-# COMPILE AGDA2HS signatureMatchedTheoremCandidates #-}
{-# COMPILE AGDA2HS stringListEqual #-}
{-# COMPILE AGDA2HS normalizedSignatureEqual #-}
{-# COMPILE AGDA2HS semanticLawIsRecordField #-}
{-# COMPILE AGDA2HS semanticLawIsReflexive #-}
{-# COMPILE AGDA2HS semanticLawNamePresent #-}
{-# COMPILE AGDA2HS recordFieldSignatureCandidate #-}
{-# COMPILE AGDA2HS signatureCandidateEdgeFor #-}
{-# COMPILE AGDA2HS signatureCandidateEdgesForFields #-}
{-# COMPILE AGDA2HS signatureCandidateEdgesForTheorems #-}
{-# COMPILE AGDA2HS dominanceEdgeEqual #-}
{-# COMPILE AGDA2HS dominanceEdgeMember #-}
{-# COMPILE AGDA2HS dedupeSignatureCandidateEdges #-}
{-# COMPILE AGDA2HS dedupeStringsWithSeen #-}
{-# COMPILE AGDA2HS dedupeStrings #-}
{-# COMPILE AGDA2HS allNamesPresent #-}
{-# COMPILE AGDA2HS semanticPlanEGraphReport #-}
{-# COMPILE AGDA2HS knownRedundancyCandidateNames #-}
{-# COMPILE AGDA2HS knownRedundancyCandidatesPresent #-}
{-# COMPILE AGDA2HS semanticPlanEGraphComplete #-}
{-# COMPILE AGDA2HS semanticPlanEGraphExtractable #-}
{-# COMPILE AGDA2HS canonicalSearchPlanEGraphClosed #-}
{-# COMPILE AGDA2HS canonicalSearchPlanEGraphSaturates #-}
{-# COMPILE AGDA2HS canonicalSearchPlanEGraphExtracts #-}
{-# COMPILE AGDA2HS graphAStarPlanEGraphClosed #-}
{-# COMPILE AGDA2HS requiredPlanEGraphCount #-}
{-# COMPILE AGDA2HS requiredPlanEGraphComplete #-}
{-# COMPILE AGDA2HS haskellMinusOneTargetCapabilities #-}
{-# COMPILE AGDA2HS haskellMinusOneLaws #-}
{-# COMPILE AGDA2HS haskellMinusOneAStar #-}
{-# COMPILE AGDA2HS haskellMinusOneAStarPlan #-}
{-# COMPILE AGDA2HS haskellMinusOneAStarComplete #-}
{-# COMPILE AGDA2HS hybridInverseExactRealPlan #-}
{-# COMPILE AGDA2HS hybridInverseExactRealSearchReport #-}
{-# COMPILE AGDA2HS agdaSemanticPortReport #-}

{-# COMPILE AGDA2HS addCapabilities #-}
{-# COMPILE AGDA2HS multiCapabilityLaw #-}
{-# COMPILE AGDA2HS multiCapabilitySearch #-}
{-# COMPILE AGDA2HS multiCapabilityCoverageRegression #-}
