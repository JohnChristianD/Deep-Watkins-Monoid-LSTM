(local fun (require :fun))

; Machine-readable audit of the two canonical monoliths only.
; This is a static trust-surface certificate, never a consistency proof.
(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda"
  ])

(assert (= (# (fun.totable (fun.range 1 2))) 2)
  "Luafun range/totable iterator protocol changed")

(local read-file (fn [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local source (file:read "*a"))
  (file:close)
  source))

(local read-line (fn [command]
  (local pipe (assert (io.popen command "r") (.. "cannot run " command)))
  (local value (pipe:read "*l"))
  (pipe:close)
  (assert value (.. "no output from " command))
  value))

(local sha256 (fn [path]
  (local line (read-line (.. "sha256sum " path)))
  (local digest (string.match line "^([0-9a-f]+)"))
  (assert digest (.. "cannot parse SHA-256 for " path))
  digest))

(local trim (fn [value]
  (string.gsub (string.gsub value "^%s+" "") "%s+$" "")))

(local lines-of (fn [source]
  (local lines [])
  (each [line (string.gmatch source "[^\n]+")]
    (table.insert lines line))
  lines))

(local starts (fn [value prefix]
  (= (string.sub value 1 (# prefix)) prefix)))

(local contains (fn [source needle]
  (not (= (string.find source needle 1 true) nil))))

(local count-where (fn [lines predicate]
  (var count 0)
  (each [_ line (ipairs lines)]
    (when (predicate line)
      (set count (+ count 1))))
  count))

(local count-postulate-statements (fn [lines]
  (count-where lines
    (fn [line]
      (local item (trim line))
      (and (not (starts item "--"))
           (or (= item "postulate") (starts item "postulate ")))))))

(local count-primitive-blocks (fn [lines]
  (count-where lines (fn [line] (= (trim line) "primitive")))))

(local count-rewrite-pragmas (fn [lines]
  (count-where lines
    (fn [line] (starts (trim line) "{-# REWRITE")))))

(local count-cubical-imports (fn [lines]
  (count-where lines
    (fn [line]
      (local item (trim line))
      (and (not (starts item "--"))
           (or (starts item "open import Cubical.")
               (starts item "open import Cubical ")
               (starts item "import Cubical.")
               (starts item "import Cubical ")))))))

(local direct-classical-postulate-count (fn [lines]
  (var postulate-indent -1)
  (var count 0)
  (each [_ raw (ipairs lines)]
    (local item (trim raw))
    (local leading (or (string.match raw "^%s*") ""))
    (local indentation (string.len leading))
    (var declaration nil)
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
  count))

(local import-inventory (fn [path]
  (local lines (lines-of (read-file path)))
  (local modules [])
  (each [_ raw (ipairs lines)]
    (local item (trim raw))
    (when (not (starts item "--"))
      (local module-name
        (or (string.match item "^open import ([^%s]+)")
            (string.match item "^import ([^%s]+)")))
      (when module-name
        (table.insert modules (.. path " -> " module-name)))))
  modules))

(local rewrite-identifiers (fn [path]
  (local lines (lines-of (read-file path)))
  (local identifiers [])
  (each [_ line (ipairs lines)]
    (local marker (string.find line "{-# REWRITE " 1 true))
    (when marker
      (local ending (string.find line "#-}" marker true))
      (when ending
        (local body (string.sub line (+ marker 12) (- ending 1)))
        (each [identifier (string.gmatch body "%S+")]
          (table.insert identifiers identifier)))))
  identifiers))

(local summary (fn [path]
  (local source (read-file path))
  (local lines (lines-of source))
  { :path path
    :sha (sha256 path)
    :postulates (count-postulate-statements lines)
    :primitiveBlocks (count-primitive-blocks lines)
    :rewritePragmas (count-rewrite-pragmas lines)
    :cubicalImports (count-cubical-imports lines)
    :withK (contains source "--with-K")
    :noGuardedness (contains source "--no-guardedness")
    :hasProp (contains source "--prop")
    :hasRewriting (contains source "--rewriting")
    :hasConfluenceCheck (contains source "--confluence-check")
    :hasTwoLevel (contains source "--two-level")
    :hasSizedTypes (contains source "--sized-types")
    :classicalPostulates (direct-classical-postulate-count lines)
    :hasRussianBasis (contains source "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis")
    :hasMarkovProjection (contains source "russianMarkovPrinciple")
    :hasECT0Projection (contains source "extendedChurchThesis0")
    :hasCountableChoiceProjection (contains source "russianCountableChoice")
  }))

(local learner (summary (. source-files 1)))
(local theorems (summary (. source-files 2)))
(local commit (read-line "git rev-parse HEAD"))
(local global-options-path ".ci/agda/global-options.txt")
(local global-options (read-file global-options-path))
(local global-options-hash (sha256 global-options-path))
(local imports [])
(each [_ path (ipairs source-files)]
  (each [_ imported (ipairs (import-inventory path))]
    (table.insert imports imported)))
(local rewrite-rules (rewrite-identifiers (. source-files 1)))
(local rendered-imports [])
(each [_ imported (ipairs imports)]
  (table.insert rendered-imports
    (string.format "    \"%s\"" imported)))

(local rendered-rewrite-rules [])
(each [_ identifier (ipairs rewrite-rules)]
  (table.insert rendered-rewrite-rules
    (string.format "    \"%s\"" identifier)))

(assert (= learner.postulates 1) "learner RUSS trust boundary changed: audit before updating certificate")
(assert (= learner.rewritePragmas 2) "learner rewrite surface changed: audit before updating certificate")
(assert (= theorems.postulates 7) "theorem monolith postulate surface changed: audit before updating certificate")
(assert (= theorems.primitiveBlocks 2) "theorem Reflection/TC primitive surface changed: audit before updating certificate")
(assert (= theorems.rewritePragmas 0) "theorem monolith rewrite surface changed: audit before updating certificate")
(assert (and learner.withK theorems.withK) "both monoliths must retain --with-K")
(assert (and learner.noGuardedness theorems.noGuardedness) "both monoliths must retain --no-guardedness")
(assert (and learner.hasProp theorems.hasProp) "both monoliths must retain --prop")
(assert (and learner.hasRewriting theorems.hasRewriting) "both monoliths must retain --rewriting")
(assert (and learner.hasConfluenceCheck theorems.hasConfluenceCheck) "both monoliths must retain --confluence-check")
(assert (and learner.hasTwoLevel theorems.hasTwoLevel) "both monoliths must retain --two-level")
(assert (and learner.hasSizedTypes theorems.hasSizedTypes) "both monoliths must retain --sized-types")
(assert (contains global-options "--level-universe") "global Agda options lost --level-universe")
(assert (not (contains global-options "--cubical")) "global Agda options unexpectedly enable cubical mode")
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
(out:write "  globalAgdaConfiguration = {\n")
(out:write (.. "    globalOptionsSha256 = \"" global-options-hash "\",\n"))
(out:write "    hasLevelUniverse = True,\n")
(out:write "    hasCubicalFlag = False,\n")
(out:write "    preservesWithK = True,\n")
(out:write "    preservesNoGuardedness = True\n")
(out:write "  },\n")
(out:write "  sources = [\n")
(out:write (string.format
  "    { path = \"%s\", sha256 = \"%s\", postulateStatements = %d, primitiveBlocks = %d, rewritePragmas = %d, cubicalImports = %d, withK = %s, noGuardedness = %s, hasProp = %s, hasRewriting = %s, hasConfluenceCheck = %s, hasTwoLevel = %s, hasSizedTypes = %s, namedClassicalPostulates = %d },\n"
  learner.path learner.sha learner.postulates learner.primitiveBlocks learner.rewritePragmas learner.cubicalImports
  (if learner.withK "True" "False") (if learner.noGuardedness "True" "False")
  (if learner.hasProp "True" "False") (if learner.hasRewriting "True" "False")
  (if learner.hasConfluenceCheck "True" "False") (if learner.hasTwoLevel "True" "False")
  (if learner.hasSizedTypes "True" "False") learner.classicalPostulates))
(out:write (string.format
  "    { path = \"%s\", sha256 = \"%s\", postulateStatements = %d, primitiveBlocks = %d, rewritePragmas = %d, cubicalImports = %d, withK = %s, noGuardedness = %s, hasProp = %s, hasRewriting = %s, hasConfluenceCheck = %s, hasTwoLevel = %s, hasSizedTypes = %s, namedClassicalPostulates = %d }\n"
  theorems.path theorems.sha theorems.postulates theorems.primitiveBlocks theorems.rewritePragmas theorems.cubicalImports
  (if theorems.withK "True" "False") (if theorems.noGuardedness "True" "False")
  (if theorems.hasProp "True" "False") (if theorems.hasRewriting "True" "False")
  (if theorems.hasConfluenceCheck "True" "False") (if theorems.hasTwoLevel "True" "False")
  (if theorems.hasSizedTypes "True" "False") theorems.classicalPostulates))
(out:write "  ],\n")
(out:write "  rewriteRuleIdentifiers = [\n")
(out:write (table.concat rendered-rewrite-rules ",\n"))
(out:write "\n  ],\n")
(out:write "  importedModulesBySource = [\n")
(out:write (table.concat rendered-imports ",\n"))
(out:write "\n  ],\n")
(out:write "  russGlobalityAudit = {\n")
(out:write "    assumptionDeclaredIn = \"FullCoupled/CanonicalLearnerMonolith.agda\",\n")
(out:write "    theoremMonolithReexportsBasis = True,\n")
(out:write "    RUSSPrinciplesAreRewriteRules = False,\n")
(out:write "    globalityStatus = \"PUBLICLY_REEXPORTED_NOT_GLOBAL_AXIOMATIC_RULES\",\n")
(out:write "    explanation = \"One record postulate packages MP, ECT0, and countable choice; named projections expose it to TheoremsMonolith. This is not a global rewrite-rule system.\"\n")
(out:write "  },\n")
(out:write "  permanentReferences = [\n")
(out:write "    \"Stanford Encyclopedia of Philosophy: Constructive Mathematics — RUSS, Markov principle, and varieties of constructivism: https://plato.stanford.edu/entries/mathematics-constructive/\",\n")
(out:write "    \"nLab: Russian constructivism — MP, dependent choice, and principles rejected by RUSS: https://ncatlab.org/nlab/show/Russian%2Bconstructivism\",\n")
(out:write "    \"Wikibooks: Supplementary mathematics — Markov principle reference: https://en.wikibooks.org/wiki/Supplementary_mathematics\"\n")
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
(out:write "    explicitClassicalPostulateFound = False,\n")
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
