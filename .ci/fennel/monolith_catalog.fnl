(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda"
  ])

(local replacements
  [ ["⊥" "Bottom"] ["→" "->"] ["＝" "="] ["≡" "="]
    ["ℕ" "Nat"] ["ℤ" "Int"] ["∀" "forall"] ["Σ" "Sigma"]
    ["λ" "lambda"] ["∷" "::"] ["×" "x"] ["∈" "in"]
  ])

(local trim (fn [value]
  (local leading (string.gsub value "^%s+" ""))
  (string.gsub leading "%s+$" "")))

(local compact (fn [value]
  (local normalized (string.gsub value "%s+" " "))
  (local stripped (trim normalized))
  (if (> (# stripped) 220)
      (let [prefix (string.sub stripped 1 217)]
        (.. prefix "..."))
      stripped)))

(local ascii-sanitize
  (fn sanitize [value index]
    (if (> index (# replacements))
        (let [safe (string.gsub value "[^ -~]" "?")]
          safe)
        (let [pair (. replacements index)]
          (let [replaced (string.gsub value (. pair 1) (. pair 2))]
            (sanitize replaced (+ index 1)))))))

(local js-escape (fn [value]
  (local slash (string.gsub value "\\" "\\\\"))
  (local quote (string.gsub slash "\"" "\\\""))
  (local newline (string.gsub quote "\n" "\\n"))
  (local carriage (string.gsub newline "\r" "\\r"))
  (string.gsub carriage "\t" "\\t")))

(local classify (fn [path name kind]
  (local lower (string.lower name))
  (if (= kind "postulate")
      (if (= name "russianRecursiveMathematicsAssumptions")
          "RUSS trust entry"
          "Explicit postulate / trust boundary")
      (if (= kind "primitive")
          "Agda reflection / TC primitive"
          (if (or (string.find lower "russian" 1 true)
                  (string.find lower "russect" 1 true)
                  (string.find lower "russcountable" 1 true)
                  (string.find lower "churchthesis" 1 true)
                  (string.find lower "markovprinciple" 1 true)
                  (string.find lower "constructivecountablechoice" 1 true))
              "RUSS assumption or consequence"
              (if (= path "FullCoupled/CanonicalLearnerMonolith.agda")
                  "Canonical learner semantics"
                  "Theorem / proof surface"))))))

(local list-append (fn list-append [xs ys]
  (if xs
      {:head xs.head :tail (list-append xs.tail ys)}
      ys)))

(local list-map (fn list-map [function xs]
  (if xs
      {:head (function xs.head) :tail (list-map function xs.tail)}
      nil)))

(local list-join (fn list-join [separator xs]
  (if xs
      (if xs.tail
          (.. xs.head separator (list-join separator xs.tail))
          xs.head)
      "")))

(local lines-of (fn lines-of [source cursor]
  (local ending (string.find source "\n" cursor true))
  (if ending
      {:head (string.sub source cursor (- ending 1))
       :tail (lines-of source (+ ending 1))}
      {:head (string.sub source cursor) :tail nil})))

(local scan-lines
  (fn scan-lines [path lines line-number postulate-indent primitive-indent]
    (if (not lines)
        nil
        (do
          (local line lines.head)
          (local leading (or (string.match line "^%s*") ""))
          (local indentation (# leading))
          (local trimmed (trim line))
          (local active-postulate
            (if (and (>= postulate-indent 0)
                     (<= indentation postulate-indent)
                     (not (= trimmed "postulate")))
                -1 postulate-indent))
          (local active-primitive
            (if (and (>= primitive-indent 0)
                     (<= indentation primitive-indent)
                     (not (= trimmed "primitive")))
                -1 primitive-indent))
          (local next-postulate
            (if (= trimmed "postulate") indentation active-postulate))
          (local next-primitive
            (if (= trimmed "primitive") indentation active-primitive))
          (local inline-postulate (string.match trimmed "^postulate%s+"))
          (local declaration-line
            (if inline-postulate
                (string.gsub trimmed "^postulate%s+" "")
                trimmed))
          (local name (string.match declaration-line "^([^:]+)%s*:"))
          (local signature (string.match declaration-line "^[^:]+:%s*(.*)$"))
          (local kind
            (if inline-postulate
                "postulate"
                (if (or (and (>= active-postulate 0)
                             (> indentation active-postulate))
                        (string.match trimmed "^postulate%s+"))
                    "postulate"
                    (if (and (>= active-primitive 0)
                             (> indentation active-primitive))
                        "primitive"
                        "ordinary"))))
          (local entry
            (if (and name
                     signature
                     (not (= trimmed ""))
                     (not (string.match trimmed "^%-%-"))
                     (not (string.match trimmed "^{-#"))
                     (not (string.match trimmed "^module%s+")))
                (let [clean-name (compact name)]
                  (let [clean-signature
                        (if (= (trim signature) "")
                            "(signature continues on following lines)"
                            (ascii-sanitize (compact signature) 1))]
                    {:id (.. path "#" clean-name ":" (tostring line-number))
                     :name (ascii-sanitize clean-name 1)
                     :source path
                     :line line-number
                     :signature clean-signature
                     :category (classify path clean-name kind)}))
                nil))
          (local rest
            (scan-lines path lines.tail (+ line-number 1)
              next-postulate next-primitive))
          (if entry {:head entry :tail rest} rest)))))

(local read-file (fn [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content))

(local collect-entries
  (fn collect-entries [index]
    (if (> index (# source-files))
        nil
        (do
          (local path (. source-files index))
          (local content (read-file path))
          (local found (scan-lines path (lines-of content 1) 1 -1 -1))
          (list-append found (collect-entries (+ index 1)))))))

(local entries (collect-entries 1))
(local rendered-entries
  (list-map
    (fn [entry]
      (string.format
        "    { id: \"%s\", name: \"%s\", source: \"%s\", line: %d, signature: \"%s\", category: \"%s\" }"
        (js-escape entry.id) (js-escape entry.name) (js-escape entry.source)
        entry.line (js-escape entry.signature) (js-escape entry.category)))
    entries))

(local rendered-sources
  (fun.totable
    (fun.map
      (fn [index]
        (string.format "    \"%s\"" (js-escape (. source-files index))))
      (fun.range 1 (# source-files))))

(local catalog-source
  (.. "export const MonolithContent = Object.freeze({\n"
      "  sourceFiles: Object.freeze([\n"
      (table.concat rendered-sources ",\n")
      "\n  ]),\n"
      "  entries: Object.freeze([\n"
      (list-join ",\n" rendered-entries)
      "\n  ].map((entry) => Object.freeze(entry)))\n"
      "});\n"))

; Deliberate I/O boundary: read source files, then write one frozen JS data module.
(local output-path (assert (. arg 1) "usage: monolith_catalog.fnl OUTPUT.mjs"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))
(output:write catalog-source)
(output:close)
(print (.. "generated immutable two-monolith catalogue: " output-path))
