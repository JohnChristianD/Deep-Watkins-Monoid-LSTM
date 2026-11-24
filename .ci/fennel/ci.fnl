(local shell-quote
  (fn [value]
    (.. "'" (string.gsub (tostring value) "'" "'\\''") "'")))

(local succeeded?
  (fn [status] (or (= status 0) (= status true))))

(local run!
  (fn [label command]
    (let [status (os.execute command)]
      (when (not (succeeded? status))
        (io.stderr:write
          (.. "ci-lane=fail: " label " (status " (tostring status) ")\n"))
        (os.exit 1)))))

(local read-file
  (fn [path]
    (let [file (assert (io.open path "r") (.. "cannot read " path))
          content (:read file "*a")]
      (:close file)
      content)))

(local write-file
  (fn [path content]
    (let [file (assert (io.open path "w") (.. "cannot write " path))]
      (:write file content)
      (:close file))))

(local check-build-source
  (fn []
    (run! "reject YueScript source files"
      "if find . -path './.git' -prune -o -type f -name '*.yue' -print -quit | grep -q .; then echo 'YueScript source remains' >&2; exit 1; fi")
    (run! "reject YueScript toolchain references"
      "if grep -Eiq 'yuescript|\\.ci/yue|\\.yue' flake.nix .github/workflows/github-pages.yml; then echo 'YueScript toolchain reference remains' >&2; exit 1; fi")
    (run! "reject contraction and replaying LuaFun iterators"
      "if grep -Eni '(^|[^[:alnum:]_])(duplicate|replicate|xrepeat|cycle|is_null|split|split_at|span|partition|tabulate|zeros|ones|rand|rands)([^[:alnum:]_]|$)' .ci/fennel/*.fnl; then echo 'forbidden iterator combinator found' >&2; exit 1; fi")
    (print "build-source-audit=pass; Fennel; basic LuaFun subset")))

(local check-agda-learner
  (fn []
    (let [source "FullCoupled/CanonicalLearnerMonolith.agda"]
      (run! "reject LSTM and epsilon-greedy paths"
        (.. "if grep -Eiq 'lstm|epsilon[ _-]?greedy|e[_-]?z[_-]?greedy' "
            (shell-quote source)
            "; then echo 'forbidden recurrent/action selector found' >&2; exit 1; fi"))
      (run! "reject DeepSets and postponed FQF code"
        (.. "if grep -Eiq 'DeepSets|FQF' " (shell-quote source)
            "; then echo 'postponed architecture found in learner source' >&2; exit 1; fi"))
      (run! "reject floating-point runtime types"
        (.. "if grep -Eiq '(^|[^[:alnum:]_])(Float|Double|Float32|Float64)([^[:alnum:]_]|$)' "
            (shell-quote source)
            "; then echo 'floating-point runtime type found' >&2; exit 1; fi"))
      (run! "require current Q8.24 learner symbols"
        (.. "for symbol in 'qShift = 24' 'qOne     = 16777216' "
            "qRelu qSarsaOneStepTarget networkTrainStepSARSA networkStep "
            "networkSequenceVJP networkApplySequenceGradient iterativeCHAD; do "
            "grep -Fq \"$symbol\" " (shell-quote source) " || exit 1; done"))
      (run! "require ReLU on recurrent output"
        (.. "grep -Fq 'hiddenAfter = qRelu mixPre' " (shell-quote source)))
      (print "learner-source-audit=pass; Q8.24; ReLU; one-step SARSA")))

(local check-agda-theorem
  (fn []
    (check-build-source)
    (run! "parallel Agda checks" "fennel .ci/fennel/parallel_agda.fnl")
    (run! "create Agda2HS output directory" "mkdir -p build/agda2hs")
    (run! "Agda2HS extract canonical learner"
      (.. "agda2hs "
          (shell-quote "FullCoupled/CanonicalLearnerMonolith.agda")
          " -o " (shell-quote "build/agda2hs")))
    (run! "verify extracted Haskell module"
      "test -s build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs")
    (run! "create GHC check output directory" "mkdir -p build/ghc")
    (run! "GHC typecheck extracted learner"
      (.. "ghc-check -fno-code -fforce-recomp -i./build/agda2hs "
          "-odir build/ghc -hidir build/ghc "
          "build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs"))
    (print "agda2hs-and-ghc-check=pass-relative-to-declared-imports-and-primitives")))

(local check-russ-audit
  (fn []
    (run! "create RUSS audit directory" "mkdir -p build")
    (run! "generate RUSS trust inventory"
      "fennel .ci/fennel/russ_audit.fnl build/russ-audit.dhall")
    (run! "typecheck RUSS inventory" "dhall type --file build/russ-audit.dhall")
    (print "russ-audit=generated; lexical inventory is not a proof certificate")))

(local check-pages
  (fn []
    (let* [out (or (os.getenv "PAGES_OUTPUT_DIR") "build/pages")
           palette (.. out "/palette.css")
           base-css (.. out "/base.css")
           css (.. out "/site.css")
           html (.. out "/index.html")]
      (run! "create static Pages output" (.. "mkdir -p " (shell-quote out)))
      (run! "generate palette CSS"
        (.. "fennel .ci/fennel/palette_css.fnl " (shell-quote palette)))
      (run! "compile Less stylesheet"
        (.. "lessc site/site.less " (shell-quote base-css)))
      (write-file css (.. (read-file palette) "\n" (read-file base-css)))
      (run! "render static HTML"
        (.. "fennel .ci/fennel/pages.fnl " (shell-quote html)))
      (let [generated-html (read-file html)
            generated-css (read-file css)]
        (assert (string.find generated-html "href=\"site.css\"" 1 true)
          "published HTML is missing its stylesheet link")
        (assert (string.find generated-html "class=\"intro\"" 1 true)
          "published HTML is missing the styled intro section")
        (assert (string.find generated-html "class=\"russ-status\"" 1 true)
          "published HTML is missing the styled RUSS status")
        (assert (string.find generated-css ".russ-status" 1 true)
          "compiled LESS is missing the RUSS status style")
        (assert (string.find generated-css ".table-wrap" 1 true)
          "compiled LESS is missing the table layout style"))
      (os.remove palette)
      (os.remove base-css)
      (print "static-pages=generated; less-css=validated; browser-JavaScript=none"))))

(local stages
  {:AgdaLearner (fn [] (check-agda-theorem) (check-agda-learner))
   :AgdaTheorem check-agda-theorem
   :RUSS (fn [] (check-agda-theorem) (check-russ-audit))
   :Pages (fn [] (check-build-source) (check-pages))
   :All (fn []
          (check-build-source)
          (check-agda-theorem)
          (check-agda-learner)
          (check-russ-audit)
          (check-pages))})

(local lane (or (. arg 1) ""))
(local action (. stages lane))
(if action
    (action)
    (do
      (io.stderr:write
        "usage: fennel .ci/fennel/ci.fnl AgdaLearner|AgdaTheorem|RUSS|Pages|All\n")
      (os.exit 2)))
