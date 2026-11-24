(local fun (require :fun))

(local source-files
  ["FullCoupled/CanonicalLearnerMonolith.agda"
   "FullCoupled/TheoremsMonolith.agda"])

(local read-file
  (fn [path]
    (let [file (assert (io.open path "r") (.. "cannot read " path))
          content (:read file "*a")]
      (:close file)
      content)))

(local lines-of
  (fn [source]
    (let [lines []]
      (each [line (string.gmatch (.. source "\\n") "(.-)\\n")]
        (table.insert lines line))
      lines)))

(local trim
  (fn [value]
    (string.gsub (string.gsub value "^%s+" "") "%s+$" "")))

(local count-postulate-blocks
  (fn [source]
    (fun.foldl
      (fn [count line]
        (let [cleaned (trim line)]
          (if (or (= cleaned "postulate") (string.match cleaned "^postulate%s+"))
              (+ count 1)
              count)))
      0
      (lines-of source))))

(local has-token
  (fn [source token]
    (not (= (string.find source token 1 true) nil))))

(local as-dhall-bool
  (fn [value] (if value "True" "False")))

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
, parametricEnumerabilityPresent = %s
, richmanCountableChoicePresent = %s
, conditionalExcludedMiddleProfilePresent = %s
, boundedMarkovSearchPresent = %s
, registerMachineEvaluatorPresent = %s
, intuitionisticObjectCalculusSoundnessPresent = %s
, objectCalculusRelativeConsistencyPresent = %s
, constructiveRiceTheoremPresent = %s
, concreteRiceProgrammingSystemPresent = False
, independentCombinedBasisModelProvided = False
, transitiveImportClosureCertified = False
, fullRUSSConsistencyCertified = False
}
]]
    (# source-files)
    learner-postulates
    theorem-postulates
    (as-dhall-bool (has-token learner "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis"))
    (as-dhall-bool (has-token learner "russParametricEnumerability"))
    (as-dhall-bool (has-token learner "russCountableChoice"))
    (as-dhall-bool (has-token theorem "excludedMiddleTheorem"))
    (as-dhall-bool (has-token theorem "russSearchBounded"))
    (as-dhall-bool (has-token learner "runMachineWithFuel"))
    (as-dhall-bool (has-token theorem "russSoundness"))
    (as-dhall-bool (has-token theorem "russCurrentBasisRelativeConsistency"))
    (as-dhall-bool (has-token theorem "RiceTheorem"))))

(output:close)
(print "russ-audit=generated; lexical inventory is not a proof certificate")
