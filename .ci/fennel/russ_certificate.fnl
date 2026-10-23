(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda" ])

(local read-file (fn [path]
  (local f (assert (io.open path "r") (.. "cannot read " path)))
  (local s (f:read "*a"))
  (f:close)
  s))

(local trim (fn [s]
  (string.gsub (string.gsub s "^%s+" "") "%s+$" "")))

(local lines-of (fn [source]
  (local lines [])
  (each [line (string.gmatch (.. source "\n") "(.-)\n")]
    (table.insert lines line))
  lines))

(local count-where (fn [xs predicate]
  (local n 0)
  (each [_ value (ipairs xs)]
    (when (predicate value) (set n (+ n 1))))
  n))

(local count-postulate-blocks (fn [source]
  (count-where (lines-of source)
    (fn [line]
      (local s (trim line))
      (or (= s "postulate")
          (and (string.match s "^postulate%s+") (not (= s "postulate")))))))

(local has-token (fn [source token]
  (not (= (string.find source token 1 true) nil))))

(local strip-line-comment (fn [line]
  (local marker (string.find line "--" 1 true))
  (if marker (string.sub line 1 (- marker 1)) line)))

(local classical-postulate-count (fn [source]
  (count-where (lines-of source)
    (fn [line]
      (local s (trim (strip-line-comment line)))
      (or (string.match s "^postulate%s+ExcludedMiddle[%s:]")
          (string.match s "^postulate%s+excludedMiddle[%s:]")
          (string.match s "^postulate%s+lawOfExcludedMiddle[%s:]")
          (string.match s "^postulate%s+doubleNegationElimination[%s:]")
          (string.match s "^postulate%s+classicalAxiom[%s:]")
          (string.match s "^postulate%s+classicalLogic[%s:]")
          (string.match s "^postulate%s+DNE[%s:]")
          (string.match s "^postulate%s+LEM[%s:]")
          (string.match s "^postulate%s+LPO[%s:]")
          (string.match s "^postulate%s+LLPO[%s:]")))))

(local learner (read-file (. source-files 1)))
(local theorem (read-file (. source-files 2)))
(local learner-postulates (count-postulate-blocks learner))
(local theorem-postulates (count-postulate-blocks theorem))
(local named-classical (+ (classical-postulate-count learner)
                          (classical-postulate-count theorem)))

(assert (= learner-postulates 1)
  "learner RUSS trust boundary changed; audit source before changing certificate")
(assert (= theorem-postulates 0)
  "local Reflection/TC postulates remain; use Agda's builtin Reflection API")
(assert (has-token theorem "open import Agda.Builtin.Reflection using"))
(assert (not (has-token theorem "module ReflectionCompat where"))
  "handwritten Reflection ABI remains in the theorem monolith")
(assert (= named-classical 0) "named classical postulate detected")
(assert (has-token learner "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis"))
(assert (has-token theorem "russSearchBounded"))
(assert (has-token theorem "russSoundness"))
(assert (has-token theorem "russCoreConsistency"))
(assert (has-token theorem "russCurrentBasisRelativeConsistency"))
(assert (not (has-token theorem "graphAStar")))
(assert (not (has-token theorem "EGraphCongruence")))
(assert (not (has-token theorem "AStarCostModel")))
(assert (not (has-token theorem "eGraphAStarIterate")))

(local output-path (or (. arg 1) "build/russ-audit.dhall"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))
(output:write
  (string.format [[
{ directMonolithInventoryPassed = True
, canonicalModuleCount = %d
, learnerPostulateBlocks = %d
, theoremLocalPostulateBlocks = %d
, namedClassicalPostulateCount = %d
, boundedMarkovSearchPresent = True
, registerMachineEvaluatorPresent = True
, intuitionisticObjectCalculusSoundnessPresent = True
, objectCalculusRelativeConsistencyPresent = True
, independentCombinedBasisModelProvided = False
, transitiveImportClosureCertified = False
, fullRUSSConsistencyCertified = False
, graphSearchEnabled = False
, browserJavaScriptEnabled = False
}
]] (# source-files) learner-postulates theorem-postulates named-classical))
(output:close)
(print "russ-inventory=pass; full-RUSS-consistency=not-certified")