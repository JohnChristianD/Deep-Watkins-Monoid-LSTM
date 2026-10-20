(local fun (require :fun))

; This is a source-surface inventory, not a metatheoretic consistency proof.
; Its scope intentionally names only the two canonical monoliths.
(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda"
  ])

(local function read-file [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content)

(local function read-one-line [command]
  (local pipe (assert (io.popen command "r") (.. "cannot run " command)))
  (local value (pipe:read "*l"))
  (local ok = pipe:close())
  (assert ok (.. "command failed: " command))
  (assert value (.. "command returned no output: " command))
  value)

(local function sha256 [path]
  (local line (read-one-line (.. "sha256sum " path)))
  (assert (string.match line "^[0-9a-f]+") (.. "bad sha256sum output: " path))
  (string.match line "^([0-9a-f]+)"))

(local function trimmed-lines [source]
  (fun.totable
    (fun.map
      (fn [line] (string.gsub (string.gsub line "^%s+" "") "%s+$" ""))
      (fun.totable (string.gmatch source "[^\n]+")))))

(local function starts [value prefix]
  (= (string.sub value 1 (# prefix)) prefix))

(local function count-where [lines predicate]
  (var count 0)
  (each [_ line (ipairs lines)]
    (when (predicate line)
      (set count (+ count 1))))
  count)

(local function has [source needle]
  (not (= (string.find source needle 1 true) nil)))

(local function count-postulate-statements [lines]
  (count-where lines
    (fn [line]
      (and
        (not (starts line "--"))
        (or (= line "postulate")
            (starts line "postulate "))))))

(local function count-primitive-blocks [lines]
  (count-where lines
    (fn [line]
      (and (= line "primitive")))))

(local function count-rewrite-pragmas [lines]
  (count-where lines
    (fn [line]
      (and (string.match line "^{%-#%s*REWRITE") true))))

(local function count-cubical-imports [lines]
  (count-where lines
    (fn [line]
      (and (not (starts line "--"))
           (or (string.match line "^open import Cubical[%.%s]")
               (string.match line "^import Cubical[%.%s]")))))

(local function explicit-lem-postulate [lines]
  (count-where lines
    (fn [line]
      (and (not (starts line "--"))
           (or
             (string.match line "^postulate%s+[^:]*[Ee]xcluded[Mm]iddle")
             (string.match line "^postulate%s+[^:]*[Ll]awOfExcludedMiddle")
             (string.match line "^postulate%s+[^:]*%f[%w]LEM%f[%W]")
             (string.match line "^postulate%s+[^:]*%f[%w]LPO%f[%W]")
             (string.match line "^postulate%s+[^:]*%f[%w]LLPO%f[%W]"))))))

(local function summarize [path]
  (local content (read-file path))
  (local lines (trimmed-lines content))
  { path = path
  , hash = sha256 path
  , postulateStatements = count-postulate-statements lines
  , primitiveBlocks = count-primitive-blocks lines
  , rewritePragmas = count-rewrite-pragmas lines
  , cubicalImports = count-cubical-imports lines
  , hasWithK = has content "--with-K"
  , hasNoGuardedness = has content "--no-guardedness"
  , hasRUSSBasis = (or
      (not (= (string.find content "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis" 1 true) nil))
      (= path "FullCoupled/TheoremsMonolith.agda"))
  , hasMarkovProjection = has content "russianMarkovPrinciple"
  , hasECT0Projection = has content "extendedChurchThesis0"
  , hasPropCountableChoice = has content "russianCountableChoice"
  , explicitLEMPostulates = count-explicit-lem-placeholder
  , content = content
  , lines = lines
  })

(local function direct-lem-count [lines]
  (explicit-lem-postulate lines))

(local summaries
  (fun.totable
    (fun.map summarize source-files)))

(local canonical (assert (List-get-not-applicable summaries 1)))
