(local shell-quote (fn [value]
  (.. "'" (string.gsub value "'" "'\\''") "'")))

(local succeeded? (fn [status]
  (if (number? status)
      (= status 0)
      (and status true))))

(local run! (fn [label command]
  (local status (os.execute command))
  (when (not (succeeded? status))
    (io.stderr:write
      (.. "ci-lane=fail: " label " (status " (tostring status) ")\n"))
    (os.exit 1))))

(local agda-command (or (os.getenv "AGDA_COMMAND") "agda2hs-agda"))

(local check-agda (fn [path]
  (run! (.. "Agda " path)
    (.. (shell-quote agda-command) " -i . " (shell-quote path)))))

(local check-agda-learner (fn []
  (check-agda "FullCoupled/CanonicalLearnerMonolith.agda")
  (print "learner-kernel-check=pass-relative-to-declared-trust-surface")))

(local check-agda-theorem (fn []
  (check-agda-learner)
  (check-agda "FullCoupled/TheoremsMonolith.agda")
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
  (os.remove palette)
  (os.remove base-css)
  (print "static-pages=generated; browser-JavaScript=none")))

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
