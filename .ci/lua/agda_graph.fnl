(local fun (require :fun))

; The presentation is a reader for exactly the two canonical monoliths.
; Do not enumerate the project-wide Agda import graph here: graph-search
; helpers and tutorial/legacy modules are not part of the documented surface.
(local source-files
  [ "FullCoupled/CanonicalLearnerMonolith.agda"
    "FullCoupled/TheoremsMonolith.agda"
  ])

(assert (= (# (fun.totable (fun.range 1 2))) 2)
  "Luafun range/totable iterator protocol changed")

(local read-file
  (fn [path]
    (local file (assert (io.open path "r") (.. "cannot read " path)))
    (local content (file:read "*a"))
    (file:close)
    content))

(local trim
  (fn [value]
    (local leading (string.gsub value "^%s+" ""))
    (string.gsub leading "%s+$" "")))

(local compact
  (fn [value]
    (local normalized (string.gsub value "%s+" " "))
    (local stripped (trim normalized))
    (if (> (# stripped) 220)
        (.. (string.sub stripped 1 217) "...")
        stripped)))

(local ascii-sanitize
  (fn [value]
    (var output value)
    ; Keep frequent Agda symbols meaningful in the ASCII-only generated
    ; Elm source; unknown non-ASCII code points become question marks.
    (each [_ pair (ipairs
        [ ["⊥" "Bottom"]
          ["→" "->"]
          ["＝" "="]
          ["≡" "="]
          ["ℕ" "Nat"]
          ["ℤ" "Int"]
          ["∀" "forall"]
          ["Σ" "Sigma"]
          ["λ" "lambda"]
          ["∷" "::"]
          ["×" "x"]
          ["∈" "in"]
        ])]
      (set output (string.gsub output (. pair 1) (. pair 2))))
    (string.gsub output "[^ -~]" "?")))

(local elm-escape
  (fn [value]
    (var escaped (string.gsub value "\\" "\\\\"))
    (set escaped (string.gsub escaped "\"" "\\\""))
    (set escaped (string.gsub escaped "\n" "\\n"))
    (set escaped (string.gsub escaped "\r" "\\r"))
    (set escaped (string.gsub escaped "\t" "\\t"))
    escaped))

(local classify (fn [path name declaration-kind]
  (local lower (string.lower name))
  (if (= declaration-kind "postulate")
      (if (= name "russianRecursiveMathematicsAssumptions")
          "RUSS trust entry"
          "Explicit postulate / trust boundary")
      (if (= declaration-kind "primitive")
          "Agda reflection / TC primitive"
          (if (or (string.find lower "russian" 1 true)
                  (string.find lower "russmarkov" 1 true)
                  (string.find lower "russect" 1 true)
                  (string.find lower "russcountable" 1 true)
                  (string.find lower "churchthesis" 1 true)
                  (string.find lower "markovprinciple" 1 true)
                  (string.find lower "constructivecountablechoice" 1 true))
              "RUSS assumption or consequence"
              (if (= path "FullCoupled/CanonicalLearnerMonolith.agda")
                  "Canonical learner semantics"
                  "Theorem / proof surface"))))))

(local source-entries (fn [path content]
  (local lines [])
  (each [line (string.gmatch content "[^\n]+")]
    (table.insert lines line))
  (local found [])
  (var postulate-indent -1)
  (var primitive-indent -1)
  (each [line-number line (ipairs lines)]
    (local leading (string.match line "^%s*"))
    (local indentation (# (or leading "")))
    (local trimmed (trim line))
    (when (and (>= postulate-indent 0)
               (<= indentation postulate-indent)
               (not (= trimmed "postulate")))
      (set postulate-indent -1))
    (when (and (>= primitive-indent 0)
               (<= indentation primitive-indent)
               (not (= trimmed "primitive")))
      (set primitive-indent -1))
    (when (= trimmed "postulate")
      (set postulate-indent indentation))
    (when (= trimmed "primitive")
      (set primitive-indent indentation))
    (local inline-postulate (string.match trimmed "^postulate%s+"))
    (local declaration-line
      (if inline-postulate
          (string.gsub trimmed "^postulate%s+" "")
          trimmed))
    (local name (string.match declaration-line "^([^:]+)%s*:"))
    (local signature
      (string.match declaration-line "^[^:]+:%s*(.*)$"))
    (when (and name
               signature
               (not (= trimmed ""))
               (not (string.match trimmed "^%-%-"))
               (not (string.match trimmed "^{-#"))
               (not (string.match trimmed "^module%s+")))
      (local clean-name (compact name))
      (local decl-kind
        (if inline-postulate
            "postulate"
            (if (or (and (>= postulate-indent 0)
                         (> indentation postulate-indent))
                    (string.match trimmed "^postulate%s+"))
                "postulate"
                (if (and (>= primitive-indent 0)
                         (> indentation primitive-indent))
                    "primitive"
                    "ordinary"))))
      (local clean-signature
        (if (= (trim signature) "")
            "(signature continues on following lines)"
            (ascii-sanitize (compact signature))))
      (table.insert found
        { :id (.. path "#" clean-name ":" (tostring line-number))
          :name (ascii-sanitize clean-name)
          :source path
          :line line-number
          :signature clean-signature
          :category (classify path clean-name decl-kind)
        })))
  found))

(local entries [])
(each [_ path (ipairs source-files)]
  (local content (read-file path))
  (each [_ entry (ipairs (source-entries path content))]
    (table.insert entries entry)))

(local rendered-entries [])
(each [_ entry (ipairs entries)]
  (table.insert rendered-entries
    (string.format
      "    { id = \"%s\", name = \"%s\", source = \"%s\", line = %d, signature = \"%s\", category = \"%s\" }"
      (elm-escape entry.id)
      (elm-escape entry.name)
      (elm-escape entry.source)
      entry.line
      (elm-escape entry.signature)
      (elm-escape entry.category))))

(local rendered-source-files
  (fun.totable
    (fun.map
      (fn [index]
        (string.format "    \"%s\"" (elm-escape (. source-files index))))
      (fun.range 1 (# source-files))))

(local output-path (assert (. arg 1) "usage: agda_graph.fnl OUTPUT.elm"))
(local output (assert (io.open output-path "w")))
(output:write "module GeneratedMonolithContent exposing (Entry, entries, sourceFiles)\n\n")
(output:write "type alias Entry =\n")
(output:write "    { id : String\n")
(output:write "    , name : String\n")
(output:write "    , source : String\n")
(output:write "    , line : Int\n")
(output:write "    , signature : String\n")
(output:write "    , category : String\n")
(output:write "    }\n\n")
(output:write "sourceFiles : List String\nsourceFiles =\n")
(output:write "[\n")
(output:write (table.concat rendered-source-files ",\n"))
(output:write "\n]\n\nentries : List Entry\nentries =\n[\n")
(output:write (table.concat rendered-entries ",\n"))
(output:write "\n]\n")
(output:close)
(print (.. "Generated the two-monolith declaration index: " output-path))
(print (.. "sources=" (# source-files) " declarations=" (# entries)))
