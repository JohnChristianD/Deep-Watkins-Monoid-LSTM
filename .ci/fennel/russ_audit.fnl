(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda" ])

(local read-file (fn [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content))

(local lines-of (fn [source]
  (let [lines []]
    (each [line (string.gmatch (.. source "\n") "(.-)\n")]
      (table.insert lines line))
    lines))

(local count-where (fn [items predicate]
  (local count 0)
  (each [_ item (ipairs items)]
    (when (predicate item)
      (set count (+ count 1))))
  count))

(local count-postulate-blocks (fn [source]
  (count-where (lines-of source)
    (fn [line]
      (local trimmed (string.gsub (string.gsub line "^%s+" "") "%s+$" ""))
      (or (= trimmed "postulate")
          (string.match trimmed "^postulate%s+"))))))

(local has-token (fn [source token]
  (not (= (string.find source token 1 true) nil))))

(local bool (fn [value]
  (if value "True" "False")))

(local learner (read-file (. source-files 1)))
(local theorem (read-file (. source-files 2)))
(local learner-postulates (count-postulate-blocks learner))
(local theorem-postulates (count-postulate-blocks theorem))

(local output-path (or (. arg 1) "build/russ-audit.dhall"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))

(output:write
  (string.format [[
{ canonicalModuleCount = %d
, learnerPostulateBlocks = %d
, theoremPostulateBlocks = %d
, learnerRUSSAssumptionsPresent = %s
, boundedMarkovSearchPresent = %s
, registerMachineEvaluatorPresent = %s
, intuitionisticObjectCalculusSoundnessPresent = %s
, objectCalculusRelativeConsistencyPresent = %s
, independentCombinedBasisModelProvided = False
, transitiveImportClosureCertified = False
, fullRUSSConsistencyCertified = False
}
]]
    (# source-files)
    learner-postulates
    theorem-postulates
    (bool (has-token learner "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis"))
    (bool (has-token theorem "russSearchBounded"))
    (bool (has-token theorem "extendedChurchThesis0"))
    (bool (has-token theorem "russSoundness"))
    (bool (has-token theorem "russCurrentBasisRelativeConsistency"))))

(output:close)
(print "russ-audit=generated; lexical inventory is not a proof certificate")
