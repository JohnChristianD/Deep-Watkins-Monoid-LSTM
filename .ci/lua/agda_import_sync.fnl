(local fun (require :fun))

(local function read-file [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content)

(local function write-file [path content]
  (local temporary (.. path ".tmp"))
  (local file (assert (io.open temporary "w") (.. "cannot write " temporary)))
  (file:write content)
  (file:close)
  (assert (os.rename temporary path) (.. "cannot replace " path)))

(local function read-lines [command]
  (local pipe (assert (io.popen command "r") (.. "cannot run " command)))
  (local lines [])
  (each [line (pipe:lines)]
    (table.insert lines line))
  (local ok (pipe:close))
  (assert ok (.. "command failed: " command))
  lines)

(local function non-comment-lines [content]
  (fun.totable
    (fun.filter
      (fn [line]
        (and (not (= line ""))
             (not (string.match line "^%s*#"))))
      (fun.totable (string.gmatch content "[^\n]+")))))

(local function count-exact-line [content expected]
  (var count 0)
  (each [line (string.gmatch content "[^\n]+")]
    (when (= line expected)
      (set count (+ count 1))))
  count)

(local function has-prefix [line prefix]
  (= (string.sub line 1 (# prefix)) prefix))

(local function sync-import [path prefix expected expected-count]
  (local original (read-file path))
  (local lines (fun.totable (string.gmatch original "[^\n]+")))
  (local rendered [])
  (var matches 0)
  (each [_ line (ipairs lines)]
    (if (has-prefix line prefix)
        (do
          (set matches (+ matches 1))
          (table.insert rendered expected))
        (table.insert rendered line)))
  (assert (= matches expected-count)
    (.. path ": expected " expected-count " line(s) with prefix '" prefix "', found " matches))
  (local output (.. (table.concat rendered "\n") "\n"))
  (when (not (= output original))
    (write-file path output)
    (print (.. "agda-import-sync=updated " path " [" prefix "]"))))

(local function count-substring [source needle]
  (var count 0)
  (var cursor 1)
  (while true
    (local found (string.find source needle cursor true))
    (if found
        (do
          (set count (+ count 1))
          (set cursor (+ found (# needle))))
        (break)))
  count)

(local function cubical-marker [line]
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

(local function check-cubical-free [files]
  (var hits 0)
  (each [_ path (ipairs files)]
    (local content (read-file path))
    (assert (not (string.find content "MIRTH-SYNC" 1 true))
      (.. path ": legacy Mirth sync marker remains"))
    (each [line-number line (ipairs (fun.totable (string.gmatch content "[^\n]+")))]
      (when (and (not (string.match line "^%s*%-%-"))
                 (cubical-marker line))
        (set hits (+ hits 1))
        (io.stderr:write
          (.. "cubical/unsafe Agda construct: " path ":" line-number ": " line "\\n")))))
  (assert (= hits 0) (.. "found " hits " cubical/unsafe construct(s); review explicitly instead of auto-deleting proof code"))
  (print (.. "agda-cubical-scan=clean (" (# files) " tracked Agda sources)")))

(local function check-runtime-closure [paths]
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

(local contract-path ".ci/agda/import-contracts.tsv")
(local contract-lines (non-comment-lines (read-file contract-path)))
(local agda-files
  (fun.totable
    (fun.filter
      (fn [path]
        (or (string.match path "%.agda$")
            (string.match path "%.lagda$")))
      (read-lines "git ls-files '*.agda' '*.lagda'"))))

(assert (> (# agda-files) 0) "no tracked Agda/Literate Agda sources found")

(when (= mode "--sync")
  (each [_ line (ipairs contract-lines)]
    (local fields (fun.totable (string.gmatch line "[^\t]+")))
    (assert (= (# fields) 5) (.. "invalid TSV row in " contract-path ": " line))
    (when (= (. fields 1) "sync")
      (local expected-count (tonumber (. fields 5)))
      (assert (= expected-count 1) "sync rows must target exactly one import line")
      (sync-import
        (. fields 2)
        (. fields 3)
        (. fields 4)
        expected-count))))

(each [_ line (ipairs contract-lines)]
  (local fields (fun.totable (string.gmatch line "[^\t]+")))
  (assert (= (# fields) 5) (.. "invalid TSV row in " contract-path ": " line))
  (local mode-kind (. fields 1))
  (local path (. fields 2))
  (local expected (. fields 4))
  (local expected-count (tonumber (. fields 5)))
  (assert (or (= mode-kind "sync") (= mode-kind "require"))
    (.. contract-path ": unsupported mode '" mode-kind "'"))
  (assert expected-count (.. contract-path ": invalid count for " path))
  (local actual-count (count-exact-line (read-file path) expected))
  (assert (= actual-count expected-count)
    (.. path ": expected exact line '" expected "' " expected-count " time(s), found " actual-count)))

(local options-path ".ci/agda/global-options.txt")
(local options (read-file options-path))
(assert (= (count-substring options "\n") 3) "shared Agda CLI options must have exactly three entries")
(assert (= (count-exact-line options "--lossy-unification") 0) "--lossy-unification is file-local and must not be shared globally")
(assert (= (count-exact-line options "--experimental-lazy-instances") 0) "--experimental-lazy-instances is file-local and must not be shared globally")
(assert (= (count-exact-line options "--sized-types") 0) "--sized-types is file-local and must not be shared globally")
(assert (= (count-exact-line options "--exact-split") 0) "--exact-split is file-local and must not be shared globally")
(assert (= (count-exact-line options "--erased-matches") 0) "--erased-matches is file-local and must not be shared globally")
(assert (= (count-exact-line options "--erase-record-parameters") 0) "--erase-record-parameters is file-local and must not be shared globally")
(assert (= (count-exact-line options "--prop") 0) "--prop is file-local and must not be shared globally")
(assert (= (count-exact-line options "--confluence-check") 0) "--confluence-check is file-local and must not be shared globally")
(assert (= (count-exact-line options "--two-level") 0) "--two-level is file-local and must not be shared globally")
(assert (= (count-exact-line options "--level-universe") 0) "--level-universe is file-local and must not be shared globally")
(assert (= (count-exact-line options "--auto-inline") 0) "--auto-inline is file-local and must not be shared globally")
(assert (= (count-exact-line options "--polarity") 0) "--polarity is file-local and must not be shared globally")
(assert (= (count-exact-line options "--cumulativity") 0) "--cumulativity is file-local and must not be shared globally")
(assert (= (count-exact-line options "--rewriting") 0) "--rewriting is file-local and must not be shared globally")
(assert (= (count-exact-line options "--flat-split") 0) "--flat-split is file-local and must not be shared globally")
(assert (= (count-exact-line options "--erasure") 1) "global options must contain --erasure exactly once")
(assert (= (count-exact-line options "--verbose=1") 1) "global options must use CLI spelling --verbose=1 exactly once")
(assert (= (count-exact-line options "-v=1") 0) "source-pragma verbosity spelling -v=1 must not be passed through the CLI wrapper")
(assert (= (count-exact-line options "--no-projection-like") 1) "global options must contain --no-projection-like exactly once")
(assert (= (count-exact-line options "--cumulativity") 0) "--cumulativity must stay file-local")
(assert (= (count-exact-line options "--rewriting") 0) "--rewriting must stay file-local")
(assert (= (count-exact-line options "--flat-split") 0) "--flat-split must stay file-local")
(assert (not (string.find options "--guardedness" 1 true))
  "--guardedness is module/lane-specific and must not be made global")

(local flake (read-file "flake.nix"))
(assert (= (count-substring flake "cp -RL") 3)
  "Agda wrappers must use writable copies of agda2hs-base for interface files")
(assert (= (count-substring flake ".ci/agda/global-options.txt") 3)
  "the Agda, Agda2HS-Agda and Agda2HS wrappers must read .ci/agda/global-options.txt")
(assert (string.find flake "name = \"agda\";" 1 true)
  "missing editor-friendly Agda wrapper")
(assert (string.find flake "agda " 1 true) "missing wrapped Agda command")
(assert (string.find flake "agda2hs " 1 true) "missing wrapped Agda2HS command")

(check-runtime-closure
  [ "FullCoupled/Agda2HsSurface.agda"
    "FullCoupled/Agda2HsSemanticExtractor.agda"
    "FullCoupled/Agda2HsTheoremGraphEGraph.agda"
    "FullCoupled/Agda2HsSemanticSearch.agda"
    "FullCoupled/Agda2HsGraphSearchCheck.agda" ])

(check-cubical-free agda-files)
(print "agda-import-sync=pass")
(print "agda-global-options=pass")
(print "agda-runtime-import-boundary=pass")
