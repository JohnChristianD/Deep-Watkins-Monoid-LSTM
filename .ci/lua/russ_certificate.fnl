(local fun (require :fun))

; Machine-readable audit of the two canonical monoliths only.
; This is a static trust-surface certificate, never a consistency proof.
(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda"
  ])

(local function read-file [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local source (file:read "*a"))
  (file:close)
  source)

(local function read-line [command]
  (local pipe (assert (io.popen command "r") (.. "cannot run " command)))
  (local value (pipe:read "*l"))
  (pipe:close)
  (assert value (.. "no output from " command))
  value)

(local function sha256 [path]
  (local line (read-line (.. "sha256sum " path)))
  (local digest (string.match line "^([0-9a-f]+)"))
  (assert digest (.. "cannot parse SHA-256 for " path))
  digest)

(local function trim [value]
  (string.gsub (string.gsub value "^%s+" "") "%s+$" ""))

(local function lines-of [source]
  (fun.totable (string.gmatch source "[^\n]+")))

(local function starts [value prefix]
  (= (string.sub value 1 (# prefix)) prefix))

(local function contains [source needle]
  (not (= (string.find source needle 1 true) nil)))

(local function count-where [lines predicate]
  (var count 0)
  (each [_ line (ipairs lines)]
    (when (predicate line)
      (set count (+ count 1))))
  count)

(local function count-postulate-statements [lines]
  (count-where lines
    (fn [line]
      (local item (trim line))
      (and (not (starts item "--"))
           (or (= item "postulate") (starts item "postulate "))))))

(local function count-primitive-blocks [lines]
  (count-where lines (fn [line] (= (trim line) "primitive"))))

(local function count-rewrite-pragmas [lines]
  (count-where lines
    (fn [line] (starts (trim line) "{-# REWRITE"))))

(local function count-cubical-imports [lines]
  (count-where lines
    (fn [line]
      (local item (trim line))
      (and (not (starts item "--"))
           (or (starts item "open import Cubical.")
               (starts item "open import Cubical ")
               (starts item "import Cubical.")
               (starts item "import Cubical "))))))

(local function direct-classical-postulate-count [lines]
  (var postulate-indent -1)
  (var count 0)
  (each [_ raw (ipairs lines)]
    (local item (trim raw))
    (local leading (or (string.match raw "^%s*") ""))
    (local indentation (string.len leading))
    (local declaration nil)
    (when (and (>= postulate-indent 0)
               (<= indentation postulate-indent)
               (not (= item "postulate")))
      (set postulate-indent -1))
    (if (= item "postulate")
        (set postulate-indent indentation)
        (if (starts item "postulate ")
            (set declaration (trim (string.sub item 11)))
            (when (and (>= postulate-indent 0)
                       (> indentation postulate-indent)
                       (not (starts item "--")))
              (set declaration item))))
    (when declaration
      (when (or (starts declaration "ExcludedMiddle ")
                (starts declaration "excludedMiddle ")
                (starts declaration "lawOfExcludedMiddle ")
                (starts declaration "LEM ")
                (starts declaration "LPO ")
                (starts declaration "LLPO "))
        (set count (+ count 1)))))
  count)

(local function summary [path]
  (local source (read-file path))
  (local lines (lines-of source))
  { path = path
  , sha = (sha256 path)
  , postulates = (count-postulate-statements lines)
  , primitiveBlocks = (count-primitive-blocks lines)
  , rewritePragmas = (count-rewrite-pragmas lines)
  , cubicalImports = (count-cubical-imports lines)
  , withK = (contains source "--with-K")
  , noGuardedness = (contains source "--no-guardedness")
  , classicalPostulates = (direct-classical-postulate-count lines)
  , hasRussianBasis = (contains source "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis")
  , hasMarkovProjection = (contains source "russianMarkovPrinciple")
  , hasECT0Projection = (contains source "extendedChurchThesis0")
  , hasCountableChoiceProjection = (contains source "russianCountableChoice")
  })

(local learner (summary (. source-files 1)))
(local theorems (summary (. source-files 2)))
(local commit (read-line "git rev-parse HEAD"))

(assert (= learner.postulates 1) "learner RUSS trust boundary changed: audit before updating certificate")
(assert (= learner.rewritePragmas 2) "learner rewrite surface changed: audit before updating certificate")
(assert (= theorems.postulates 7) "theorem monolith postulate surface changed: audit before updating certificate")
(assert (= theorems.primitiveBlocks 2) "theorem Reflection/TC primitive surface changed: audit before updating certificate")
(assert (= theorems.rewritePragmas 0) "theorem monolith rewrite surface changed: audit before updating certificate")
(assert (and learner.withK theorems.withK) "both monoliths must retain --with-K")
(assert (and learner.noGuardedness theorems.noGuardedness) "both monoliths must retain --no-guardedness")
(assert (= learner.cubicalImports 0) "cubical import detected in learner monolith")
(assert (= theorems.cubicalImports 0) "cubical import detected in theorem monolith")
(assert (= learner.classicalPostulates 0) "named classical axiom declaration detected in learner monolith")
(assert (= theorems.classicalPostulates 0) "named classical axiom declaration detected in theorem monolith")
(assert learner.hasRussianBasis "single named RUSS trust entry not found")
(assert (and learner.hasMarkovProjection learner.hasECT0Projection learner.hasCountableChoiceProjection)
  "one or more public RUSS projections are missing")

(local out (assert (io.open ".ci/discovery/russ-global-certificate.dhall" "w")))
(out:write "{\n")
(out:write "  certificateKind = \"direct-monolith-trust-surface-inventory\",\n")
(out:write "  status = \"DIRECT_SURFACE_INVENTORIED; TRANSITIVE_CONSISTENCY_NOT_PROVED\",\n")
(out:write (.. "  sourceCommit = \"" commit "\",\n"))
(out:write "  sources = [\n")
(out:write (string.format
  "    { path = \"%s\", sha256 = \"%s\", postulateStatements = %d, primitiveBlocks = %d, rewritePragmas = %d, cubicalImports = %d, withK = %s, noGuardedness = %s, namedClassicalPostulates = %d },\n"
  learner.path learner.sha learner.postulates learner.primitiveBlocks learner.rewritePragmas learner.cubicalImports
  (if learner.withK "True" "False") (if learner.noGuardedness "True" "False") learner.classicalPostulates))
(out:write (string.format
  "    { path = \"%s\", sha256 = \"%s\", postulateStatements = %d, primitiveBlocks = %d, rewritePragmas = %d, cubicalImports = %d, withK = %s, noGuardedness = %s, namedClassicalPostulates = %d }\n"
  theorems.path theorems.sha theorems.postulates theorems.primitiveBlocks theorems.rewritePragmas theorems.cubicalImports
  (if theorems.withK "True" "False") (if theorems.noGuardedness "True" "False") theorems.classicalPostulates))
(out:write "  ],\n")
(out:write "  russianBasis = {\n")
(out:write "    singlePostulatedEntry = \"russianRecursiveMathematicsAssumptions\",\n")
(out:write "    markovPrincipleProjection = \"russianMarkovPrinciple\",\n")
(out:write "    churchThesisProjection = \"extendedChurchThesis0 (finite register-machine relation)\",\n")
(out:write "    countableChoiceProjection = \"russianCountableChoice (Prop-valued)\",\n")
(out:write "    basisExists = True\n")
(out:write "  },\n")
(out:write "  auditChecks = {\n")
(out:write "    directMonolithInventoryPassed = True,\n")
(out:write "    explicitExcludedMiddlePostulateFound = False,\n")
(out:write "    cubicalImportsFound = False,\n")
(out:write "    learnerRewriteSurfaceCount = 2,\n")
(out:write "    theoremReflectionPrimitiveBlocks = 2,\n")
(out:write "    emptyTypeAStarAndEGraphSearchIsConsistencyProof = False,\n")
(out:write "    transitiveImportedDependencyClosureCertified = False,\n")
(out:write "    jointConsistencyProved = False\n")
(out:write "  },\n")
(out:write "  externalTrustBoundaries = [\n")
(out:write "    \"Haskell.Prelude and Haskell.Law imported type/rewriting interface\",\n")
(out:write "    \"Agda primitive builtin and Reflection/TC ABI surface in TheoremsMonolith\",\n")
(out:write "    \"MLTT.Plus and Ordinals.Notions imports\",\n")
(out:write "    \"TWA.Thesis.Chapter3.ClosenessSpaces and SearchableTypes imports\",\n")
(out:write "    \"Agda checker implementation and the configured termination, positivity, universe, and rewrite options\"\n")
(out:write "  ],\n")
(out:write "  limitation = \"This verifies a bounded lexical inventory of the two monoliths at the recorded source hashes. It does not kernel-check the monoliths as a whole, prove their transitive dependencies consistent, or prove consistency of RUSS plus ECT0 and countable choice. A failure to find a bottom inhabitant is not a consistency proof.\"\n")
(out:write "}\n")
(out:close)
(print "russ-global-certificate=generated; transitive-consistency=not-proved")
