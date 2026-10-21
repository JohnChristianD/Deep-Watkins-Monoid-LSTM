(local fun (require :fun))

(fn read-file [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content)

(fn write-file [path content]
  (local temporary (.. path ".tmp"))
  (local file (assert (io.open temporary "w") (.. "cannot write " temporary)))
  (file:write content)
  (file:close)
  (assert (os.rename temporary path) (.. "cannot replace " path)))

(fn read-lines [command]
  (local pipe (assert (io.popen command "r") (.. "cannot run " command)))
  (local lines [])
  (each [line (pipe:lines)]
    (table.insert lines line))
  (local ok (pipe:close))
  (assert ok (.. "command failed: " command))
  lines)

(fn non-comment-lines [content]
  (fun.totable
    (fun.filter
      (fn [line]
        (and (not (= line ""))
             (not (string.match line "^%s*#"))))
      (fun.totable (string.gmatch content "[^\n]+")))))

(fn count-substring [source needle]
  (var count 0)
  (var cursor 1)
  (var found (string.find source needle cursor true))
  (while found
    (set count (+ count 1))
    (set cursor (+ found (# needle)))
    (set found (string.find source needle cursor true)))
  count)


(fn split-preserving-empty-lines [source]
  (local lines [])
  (var cursor 1)
  (while true
    (local ending (string.find source "\n" cursor true))
    (if ending
        (do
          (table.insert lines (string.sub source cursor (- ending 1)))
          (set cursor (+ ending 1)))
        (do
          (when (<= cursor (# source))
            (table.insert lines (string.sub source cursor)))
          (break))))
  lines)

(fn cubical-marker [line]
  (or
    (string.match line "^%s*open%s+import%s+Cubical%.")
    (string.match line "^%s*open%s+import%s+Cubical%s")
    (string.match line "^%s*import%s+Cubical%.")
    (string.match line "^%s*import%s+Cubical%s")
    (string.find line "Agda.Builtin.Cubical" 1 true)
    (string.find line "--cubical" 1 true)
    (string.find line "primTrustMe" 1 true)
    (string.find line "primTransp" 1 true)
    (string.find line "primHComp" 1 true)
    (string.find line "primComp" 1 true)
    (string.find line "primGlue" 1 true)
    (string.find line "primUnglue" 1 true)
    (string.find line "primINeg" 1 true)
    (string.find line "primIMin" 1 true)
    (string.find line "primIMax" 1 true)
    (string.find line "primFaceForall" 1 true)
    (string.find line "primIsOne" 1 true)
    (string.find line "primPOr" 1 true)
    (string.find line "primSubOut" 1 true)
    (string.find line "primSubIn" 1 true)))

(fn redundant-prelude-builtin [imported]
  (or (= imported "Agda.Builtin.Equality")
      (= imported "Agda.Builtin.Nat")
      (= imported "Agda.Builtin.Bool")
      (= imported "Agda.Builtin.List")
      (= imported "Agda.Builtin.Unit")))

(fn check-redundant-prelude-builtins [files]
  (var hits 0)
  (each [_ path (ipairs files)]
    (local content (read-file path))
    (each [line-number line (ipairs (fun.totable (string.gmatch content "[^\n]+")))]
      (local imported
        (or
          (string.match line "^%s*open%s+import%s+([^%s]+)")
          (string.match line "^%s*import%s+([^%s]+)")))
      (when (and imported (redundant-prelude-builtin imported))
        (set hits (+ hits 1))
        (io.stderr:write
          (.. "redundant Agda builtin; use Haskell.Prelude: "
              path ":" line-number ": " imported "\n")))))
  (assert (= hits 0)
    (.. "found " hits
        " direct imports of builtins replaced by Haskell.Prelude"))
  (print (.. "agda-prelude-builtin-migration=clean (" (# files)
             " tracked Agda sources)")))

(fn check-cubical-free [files]
  (var hits 0)
  (each [_ path (ipairs files)]
    (local content (read-file path))
    (assert (not (string.find content "MIRTH-SYNC" 1 true))
      (.. path ": legacy Mirth sync marker remains"))
    (assert (not (string.find content "Mirth" 1 true))
      (.. path ": stale Mirth reference remains after migration"))
    (assert (not (string.find content "AGDA_COMMAND" 1 true))
      (.. path ": per-file command comment remains; use the Nix Agda wrapper"))
    (each [line-number line (ipairs (fun.totable (string.gmatch content "[^\n]+")))]
      (when (and (not (string.match line "^%s*%-%-"))
                 (cubical-marker line))
        (set hits (+ hits 1))
        (io.stderr:write
          (.. "cubical/unsafe Agda construct: " path ":" line-number ": " line "\n")))))
  (assert (= hits 0) (.. "found " hits " cubical/unsafe construct(s); review explicitly instead of auto-deleting proof code"))
  (print (.. "agda-cubical-scan=clean (" (# files) " tracked Agda sources)")))

(fn check-runtime-closure [paths]
  (each [_ path (ipairs paths)]
    (local content (read-file path))
    (assert (string.find content "open import Haskell.Prelude" 1 true)
      (.. path ": missing Haskell.Prelude"))
    (assert (not (string.find content "Unsafe.Haskell" 1 true))
      (.. path ": Unsafe.Haskell is outside the trusted extraction boundary"))
    (each [line (string.gmatch content "[^\n]+")]
      (local imported
        (or
          (string.match line "^%s*open%s+import%s+([^%s]+)")
          (string.match line "^%s*import%s+([^%s]+)")))
      (when imported
        (assert (not (string.match imported "^Integers[.]"))
          (.. path ": legacy arithmetic import is outside the executable runtime closure"))
        (assert (not (string.match imported "^Naturals[.]"))
          (.. path ": legacy arithmetic import is outside the executable runtime closure"))
        (assert (not (string.match imported "^UF[.]"))
          (.. path ": legacy proof-library import is outside the executable runtime closure"))))))

(local mode (or (. arg 1) "--check"))
(assert (or (= mode "--check") (= mode "--sync"))
  "usage: agda_import_sync.fnl [--check|--sync]")

(local agda-files
  (fun.totable
    (fun.filter
      (fn [path]
        (or (string.match path "%.agda$")
            (string.match path "%.lagda$")))
      (read-lines "git ls-files '*.agda' '*.lagda'"))))

(assert (> (# agda-files) 0) "no tracked Agda/Literate Agda sources found")

; The canonical learner's merged import block is the source of truth. Sync
; visibility generically from that block instead of mirroring every import in
; a sidecar TSV.
(local learner-path "FullCoupled/CanonicalLearnerMonolith.agda")
(local learner-source (read-file learner-path))
(local public-import-marker "-- Merged external import surface; internal FullCoupled imports remain module-local.")
(assert (= (count-substring learner-source public-import-marker) 1)
  "canonical learner public import block marker must occur exactly once")
(assert (= (count-substring learner-source "open import Agda.Primitive using (Level)") 1)
  "canonical learner public import block must end at the primitive import boundary")
(local normalize-public-import-surface
  (fn [source]
    (local lines (split-preserving-empty-lines source))
    (local rendered [])
    (var in-public-surface false)
    (each [_ line (ipairs lines)]
      (when (string.find line public-import-marker 1 true)
        (set in-public-surface true))
      (when (and in-public-surface
                 (string.match line "^open import Agda%.Primitive"))
        (set in-public-surface false))
      (if (and in-public-surface
               (or (string.match line "^open import Haskell%.")
                   (string.match line "^open import Agda%.Builtin%.Equality%.Rewrite")
                   (string.match line "^open import Agda%.Builtin%.Size")))
          (if (string.find line " public" 1 true)
              (table.insert rendered line)
              (let [using-pos (string.find line " using (" 1 true)
                    hiding-pos (string.find line " hiding (" 1 true)
                    insertion-pos
                      (if (and using-pos hiding-pos)
                          (math.min using-pos hiding-pos)
                          (or using-pos hiding-pos))]
                (table.insert rendered
                  (if insertion-pos
                      (.. (string.sub line 1 (- insertion-pos 1))
                          " public"
                          (string.sub line insertion-pos))
                      (.. line " public")))))
          (table.insert rendered line)))
    (.. (table.concat rendered "\n")
        (if (string.match source "\n$") "\n" ""))))

(local normalized-learner (normalize-public-import-surface learner-source))
(if (= mode "--sync")
    (when (not (= learner-source normalized-learner))
      (write-file learner-path normalized-learner)
      (print "agda-import-sync=updated canonical learner public-import surface"))
    (assert (= learner-source normalized-learner)
      "canonical learner public-import surface is not normalized; run nix run .#agda-import-sync -- --sync"))

; Derive the Agda2HS execution boundary from tracked source names instead of
; maintaining a parallel list of modules.
(local runtime-agda-files
  (fun.totable
    (fun.filter
      (fn [path]
        (string.match path "^FullCoupled/Agda2Hs[^/]*%.agda$"))
      agda-files)))
(assert (> (# runtime-agda-files) 0)
  "no tracked Agda2HS runtime modules found")

(local forbidden-learner-builtins
  ["Agda.Builtin.Reflection" "Agda.Builtin.Coinduction"])
(local check-canonical-builtin-boundary
  (fn [path]
    (local lines (fun.totable (string.gmatch (read-file path) "[^\n]+")))
    (each [line-number line (ipairs lines)]
      (local imported
        (or
          (string.match line "^%s*open%s+import%s+([^%s]+)")
          (string.match line "^%s*import%s+([^%s]+)")))
      (when imported
        (each [_ forbidden (ipairs forbidden-learner-builtins)]
          (assert (not (= imported forbidden))
            (.. path ":" line-number
                ": learner monolith must not import " forbidden
                "; reflection stays in the theorem monolith")))))))

(check-canonical-builtin-boundary learner-path)

(local options-path ".ci/agda/global-options.txt")
(local options (read-file options-path))
(local global-option-lines (non-comment-lines options))
(assert (> (# global-option-lines) 0)
  "shared Agda CLI options file must not be empty")
; Each line is passed unchanged by all three Nix wrappers. Validate format and
; the selected non-cubical mode without duplicating the option inventory here.
; GHC language extensions are left to Nixpkgs defaults and agda2hs-generated
; LANGUAGE pragmas; this file only configures the Agda CLI.
(each [_ option (ipairs global-option-lines)]
  (assert (string.match option "^%-%-[^%s]+$")
    (.. "global Agda options must be one long CLI token per line: " option))
  (assert (not (string.match option "^%-%-cubical"))
    (.. "project global Agda options must remain non-cubical: " option)))

(local flake (read-file "flake.nix"))
(assert (= (count-substring flake "cp -RL") 3)
  "Agda wrappers must use writable copies of agda2hs-base for interface files")
(assert (= (count-substring flake ".ci/agda/global-options.txt") 3)
  "the Agda, Agda2HS-Agda and Agda2HS wrappers must read .ci/agda/global-options.txt")
(assert (string.find flake "name = \"agda\";" 1 true)
  "missing editor-friendly Agda wrapper")
(assert (string.find flake "agda " 1 true) "missing wrapped Agda command")
(assert (string.find flake "agda2hs " 1 true) "missing wrapped Agda2HS command")

(check-runtime-closure runtime-agda-files)

; The Dhall script map is the single source of truth for CI lanes. Check every
; workflow caller against it so a renamed/removed lane cannot become dormant.
(local actions-source (read-file ".ci/actions_ci.dhall"))
(local workflow-source (read-file ".github/workflows/nix-composition.yml"))
(local scripts-start
  (assert (string.find actions-source "let scripts = {" 1 true)
    "Dhall CI script map is missing"))
(local scripts-end
  (assert (string.find actions-source "\\n  ''}\\n\\nlet ScriptEntry" scripts-start true)
    "Dhall CI script map boundary is missing"))
(local scripts-body (string.sub actions-source scripts-start (- scripts-end 1)))
(local script-lanes {})
(var script-lane-count 0)
(each [_ line (ipairs (fun.totable (string.gmatch scripts-body "[^\\n]+")))]
  (local lane
    (or
      (string.match line "^  ([A-Za-z][A-Za-z0-9_]*) = ''")
      (string.match line "''[,]%s+([A-Za-z][A-Za-z0-9_]*) = ''")))
  (when lane
    (assert (not (. script-lanes lane))
      (.. "duplicate Dhall CI lane: " lane))
    (tset script-lanes lane true)
    (set script-lane-count (+ script-lane-count 1))))
(assert (> script-lane-count 0) "no Dhall CI lanes discovered")
(each [lane (string.gmatch workflow-source "run_lane%s+([A-Za-z][A-Za-z0-9_]*)")]
  (assert (. script-lanes lane)
    (.. "workflow calls missing Dhall CI lane: " lane)))
(local policy-line
  (assert (string.match workflow-source "[^\\n]*CI_LANE:[^\\n]*")
    "workflow Versions lane is missing"))
(local policy-lane
  (assert (string.match policy-line "\\\"([A-Za-z][A-Za-z0-9_]*)\\\"")
    "could not derive policy lane from workflow"))
(assert (. script-lanes policy-lane)
  (.. "workflow policy selects missing Dhall CI lane: " policy-lane))
(print (.. "dhall-ci-lane-contract=pass lanes=" script-lane-count))

(check-redundant-prelude-builtins agda-files)
(check-cubical-free agda-files)
(print "agda-import-sync=pass")
(print "agda-global-options=pass")
(print "agda-runtime-import-boundary=pass")
