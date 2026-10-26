(local read-file
  (fn [path]
    (local file (assert (io.open path "r") (.. "cannot read " path)))
    (local content (file:read "*a"))
    (file:close)
    content))

(local write-file
  (fn [path content]
    (local file (assert (io.open path "w") (.. "cannot write " path)))
    (file:write content)
    (file:close)))

(local trim (fn [s]
  (string.gsub (string.gsub s "^%s+" "") "%s+$" "")))

(local escape-html (fn [s]
  (let [amp (string.gsub s "&" "&amp;")]
    (let [lt (string.gsub amp "<" "&lt;")]
      (let [gt (string.gsub lt ">" "&gt;")]
        (let [quoted (string.gsub gt "\"" "&quot;")]
          (string.gsub quoted "'" "&#39;")))))))
(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda" ])

(local fun (require :fun))

(local is-declaration-line (fn [line]
  (and
    (= (type line) "string")
    (> (string.len line) 0)
    (= (string.match line "^%S") (string.sub line 1 1))
    (not (string.match line "^%-%-"))
    (not (= (string.sub line 1 3) "{-#"))
    (not (string.match line "^module%s+"))
    (not (string.match line "^open%s+"))
    (not (string.match line "^infix"))
    (not (string.match line "^syntax%s+"))
    (not (string.match line "^pattern%s+"))
    (not (string.match line "^postulate%s*$"))
    (not (string.match line "^primitive%s*$"))
    (string.match line "^([^:]+)%s*:")
    (string.match line "^[^:]+:%s*(.*)$"))))

(local declaration-row (fn [path line]
  (let [clean-name (trim (string.match line "^([^:]+)%s*:"))
        clean-signature (trim (string.match line "^[^:]+:%s*(.*)$"))]
    (string.format
      "<tr><td><code>%s</code></td><td><code>%s</code></td><td><code>%s</code></td></tr>"
      (escape-html path)
      (escape-html clean-name)
      (escape-html (if (= clean-signature "") "(signature continues)" clean-signature))))))

(local declaration-rows (fn [path source]
  (fun.totable
    (fun.map
      (fn [line] (declaration-row path line))
      (fun.filter is-declaration-line
        (string.gmatch (.. source "\n") "(.-)\n"))))))
(local render-section (fn [path title]
  (local rows (declaration-rows path (read-file path)))
  (string.format
    "<section class=\"section\"><h2>%s</h2><p>Source: <code>%s</code>. Entries are extracted from source text; extraction is not a proof certificate.</p><div class=\"table-wrap\"><table><thead><tr><th>Source</th><th>Declaration</th><th>Signature prefix</th></tr></thead><tbody>%s</tbody></table></div></section>"
    (escape-html title)
    (escape-html path)
    (table.concat rows "\n"))))

(local generated-content
  (table.concat
    [ "<main class=\"shell\">"
      "<header class=\"masthead\"><p class=\"eyebrow\">Agda / RUSS / static Pages</p><p><code>MLTT / Agda2HS</code></p></header>"
      "<section class=\"intro\"><h1>Canonical learner and theorem monoliths</h1><p>This page is generated at build time by Fennel from exactly two Agda sources. Published artifact contains static HTML and CSS only: no browser JavaScript, client search, graph-search runtime, Elm, or generated Agda JavaScript.</p><p class=\"russ-status\"><strong>Global RUSS consistency: not certified.</strong> The object-calculus relative consistency result is conditional on the explicitly postulated RUSS basis. It does not establish consistency of Agda, its full import closure, or the combined basis.</p></section>"
      "<section class=\"section\"><h2>Computational interpretation of selected RUSS principles</h2><dl>"
      "<dt>Markov principle for decidable predicates</dt><dd><code>russSearchBounded</code> structurally examines indices through a finite fuel bound. It returns a witness with evidence when found, otherwise reports bounded-prefix exhaustion. It never claims unbounded termination by ordinary reduction.</dd>"
      "<dt>Forster-style parametric enumerability</dt><dd><code>ParametricEnumerability</code> is a uniform function-family/SCT-style interface associated with Forster's EA equivalence in CIC, not a literal port of his impredicative Prop model. The old CPF program-selection axiom is removed; CPF data types remain as operational semantics. ECT₀ is derived from uniform enumeration when pointwise witnesses are supplied.</dd>"
      "<dt>Richman's countable choice</dt><dd><code>russCountableChoice</code> is restored as a proposition-valued assumption in the full RUSS profile. It is distinct from <code>constructiveCountableChoice</code>, which selects already supplied Set-valued witnesses. The choice-bearing profile does not include excluded middle or dependent choice.</dd>"
      "<dt>Excluded middle</dt><dd><code>excludedMiddleTheorem</code> is conditional on an explicit <code>ForsterClassicalExtension</code>. Parametric enumerability alone does not derive excluded middle, and this classical/no-choice profile omits Richman's countable choice.</dd>"
      "<dt>Rewrite-rule boundary</dt><dd>Logical assumptions are not rewritten into computational equations. Agda rewrite rules require suitable equality proofs and computational right-hand sides. The source comments preserve this trust-boundary rule.</dd>"
      "<dt>Separate metatheory</dt><dd><code>russSoundness</code> interprets derivations of the small intuitionistic object calculus in a model built from a supplied basis. <code>russCoreConsistency</code> proves that this calculus cannot derive its false formula, relative to that basis. An independent model of the combined basis and complete imported theory is still absent.</dd>"
      "</dl></section>"
      "<section class=\"section\"><h2>Constructive Rice theorem</h2><p><code>RiceTheorem.riceNoDecider</code> exposes the existing proved abstract theorem: a nontrivial extensional property over a supplied acceptable-programming system has no total decision procedure. The proof is intuitionistic and uses a fixed-point law, not excluded middle. The concrete register-machine instance is not certified yet because a universal interpreter and proved fixed-point construction remain missing.</p></section>"
      "<section class=\"section\"><h2>Rational representation boundary</h2><p>Agda2HS Prelude exports <code>Integer</code> but does not expose <code>Rational</code>. <code>RationalCode</code> stores a signed numerator and denominator-minus-one; the represented denominator is positive by construction. Codes are not gcd-normalized or a quotient type. Cross-product comparison and strict code equality are named separately. No exact-real completion is asserted.</p></section>"
      "<section class=\"section\"><h2>Proof-checking boundary</h2><p>Agda's kernel checks typed declarations relative to imports, postulates, reflection/TC primitives, compiler ABI, rewrite rules, and options. Rewrite confluence checks do not supply a model of RUSS or certify consistency of the whole theory.</p><p>Search heuristics were removed rather than presented as theorem discovery. Only a checked Agda term, together with its hypotheses and trust surface, certifies a derivation relative to the checker.</p></section>"
      (render-section "FullCoupled/CanonicalLearnerMonolith.agda" "Canonical learner semantics")
      (render-section "FullCoupled/TheoremsMonolith.agda" "Theorem and proof monolith")
      "<footer class=\"footer\"><p>Source-first index. Signatures are prefixes; consult the Agda files for complete terms and proofs.</p></footer>"
      "</main>" ]
    "\n"))

(local template (read-file "index.html"))
(local output-path (assert (. arg 1) "usage: pages.fnl OUTPUT.html"))
(local replace-region (fn [source start-marker end-marker replacement]
  (local start (assert (string.find source start-marker 1 true)
    (.. "missing template marker: " start-marker)))
  (local content-start (+ start (string.len start-marker)))
  (local finish (assert (string.find source end-marker content-start true)
    (.. "missing template marker: " end-marker)))
  (.. (string.sub source 1 (- start 1))
      replacement
      (string.sub source (+ finish (string.len end-marker)))))

(local rendered
  (replace-region
    template
    "<!-- GENERATED_CONTENT_START -->"
    "<!-- GENERATED_CONTENT_END -->"
    generated-content))
(assert (not (= rendered template)) "index.html template marker was not replaced")
(assert (not (string.find rendered "<script" 1 true)) "published HTML must not contain script elements")
(assert (string.find rendered "Global RUSS consistency: not certified" 1 true)
  "consistency boundary is missing")
(assert (string.find rendered "Canonical learner semantics" 1 true)
  "learner source section is missing")
(assert (string.find rendered "Theorem and proof monolith" 1 true)
  "theorem source section is missing")
(write-file output-path rendered)
(print (.. "static-pages=generated source-modules=" (# source-files)))