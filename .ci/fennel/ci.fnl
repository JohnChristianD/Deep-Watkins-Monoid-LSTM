(local shell-quote (fn [value]
  (.. "'" (string.gsub value "'" "'\\''") "'")))

(local succeeded? (fn [status]
  (or (= status 0) (= status true))))

(local run! (fn [label command]
  (local status (os.execute command))
  (when (not (succeeded? status))
    (io.stderr:write
      (.. "ci-lane=fail: " label " (status " (tostring status) ")\n"))
    (os.exit 1))))

(local agda-command (or (os.getenv "AGDA_COMMAND") "agda2hs-agda"))

(local check-agda (fn [path]
  (run! (.. "Agda " path)
    (.. (shell-quote agda-command) " --trace-imports=0 -i . " (shell-quote path)))))

(local check-agda-learner (fn []
  (local source "FullCoupled/CanonicalLearnerMonolith.agda")
  (check-agda source)
  (run! "forbid LSTM and epsilon-greedy source paths"
    (.. "if grep -Eiq 'lstm|epsilon[ _-]?greedy|e[_-]?z[ _-]?greedy' "
        (shell-quote source)
        "; then echo 'forbidden recurrent/action selector found' >&2; exit 1; fi"))
  (run! "forbid floating-point runtime types"
    (.. "if grep -Eiq '(^|[^[:alnum:]_])(Float|Double|Float32|Float64)([^[:alnum:]_]|$)' "
        (shell-quote source)
        "; then echo 'floating-point runtime type found' >&2; exit 1; fi"))
  (run! "require explicit Agda fixed-width representations"
    (.. "for width in Int32 Int64 Word32 Word64; do "
        "grep -Fq \"COMPILE AGDA2HS $width existing\" " (shell-quote source)
        " || exit 1; done"))
  (run! "require composed network, CHAD, and UTD2 entry points"
    (.. "for symbol in networkStep networkStepVJP networkSequenceVJP "
        "networkMunchausenSarsa3Target networkTrainSampleFromTarget "
        "networkTrainSequenceVJP networkTrainStepUTD2 networkTrainChunkUTD2 "
        "iterativeCHAD-forward-count iterativeCHAD-reverse-count "
        "iterativeCHAD-merge-count qQuantileHuberLoss "
        "qFQFFractionLogitDirection qObgdUpdate; do "
        "grep -Fq \"$symbol\" " (shell-quote source)
        " || exit 1; done"))
  (print "learner-kernel-check=pass-relative-to-declared-trust-surface")))

(local check-agda-theorem (fn []
  (run! "parallel typecheck of both Agda monoliths"
    "fennel .ci/fennel/parallel-agda.fnl")
  (run! "create agda2hs output directory" "mkdir -p build/agda2hs")
  (run! "extract canonical CHAD RNN module"
    (.. "agda2hs "
        (shell-quote "FullCoupled/CanonicalLearnerMonolith.agda")
        " -o "
        (shell-quote "build/agda2hs")))
  (run! "verify extracted canonical Haskell module"
    "test -s build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs")
  (run! "create GHC typecheck output directory" "mkdir -p build/ghc")
  (run! "GHC typecheck extracted canonical module"
    "ghc -fno-code -fforce-recomp -i./build/agda2hs -odir build/ghc -hidir build/ghc build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs")
  (print "theorem-kernel-check=pass-relative-to-imports-postulates-primitives-and-options")))

(local read-file (fn [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content))

(local write-file (fn [path content]
  (local file (assert (io.open path "w") (.. "cannot write " path)))
  (file:write content)
  (file:close)))

(local check-russ-audit (fn []
  (run! "create RUSS audit output directory" "mkdir -p build")
  (run! "RUSS trust inventory"
    "fennel .ci/fennel/russ_audit.fnl build/russ-audit.dhall")
  (run! "Dhall RUSS audit typecheck"
    "dhall type --file build/russ-audit.dhall")
  (print "russ-audit=generated; full-consistency=not-certified")))

(local check-pages (fn []
  (local out (or (os.getenv "PAGES_OUTPUT_DIR") "build/pages"))
  (local palette (.. out "/palette.css"))
  (local base-css (.. out "/base.css"))
  (local css (.. out "/site.css"))
  (local html (.. out "/index.html"))
  (run! "create Pages output" (.. "mkdir -p " (shell-quote out)))
  (run! "generate palette CSS"
    (.. "fennel .ci/fennel/palette_css.fnl " (shell-quote palette)))
  (run! "compile Less stylesheet"
    (.. "lessc site/site.less " (shell-quote base-css)))
  (write-file css (.. (read-file palette) "\n" (read-file base-css)))
  (run! "render static HTML"
    (.. "fennel .ci/fennel/pages.fnl " (shell-quote html)))
  (local generated-html (read-file html))
  (local generated-css (read-file css))
  (assert (string.find generated-html "href=\"site.css\"" 1 true)
    "published HTML is missing its stylesheet link")
  (assert (string.find generated-html "class=\"intro\"" 1 true)
    "published HTML is missing the styled intro section")
  (assert (string.find generated-html "class=\"russ-status\"" 1 true)
    "published HTML is missing the styled RUSS status")
  (assert (string.find generated-css ".russ-status" 1 true)
    "compiled LESS is missing the RUSS status style")
  (assert (string.find generated-css ".table-wrap" 1 true)
    "compiled LESS is missing the table layout style")
  (os.remove palette)
  (os.remove base-css)
  (print "static-pages=generated; less-css=validated; browser-JavaScript=none")))

(local lanes
  {"AgdaLearner" check-agda-learner
   "AgdaTheorem" check-agda-theorem
   "RUSS" (fn [] (check-agda-theorem) (check-russ-audit))
   "Pages" check-pages
   "All" (fn [] (check-agda-theorem) (check-russ-audit) (check-pages))})

(local lane (or (. arg 1) ""))
(local action (. lanes lane))
(if action
    (action)
    (do
      (io.stderr:write
        "usage: fennel .ci/fennel/ci.fnl AgdaLearner|AgdaTheorem|RUSS|Pages|All\n")
      (os.exit 2)))
