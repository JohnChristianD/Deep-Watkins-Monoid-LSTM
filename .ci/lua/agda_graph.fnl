(local fun (require :fun))
(local read-lines
  (fn [command]
  (local pipe (assert (io.popen command "r")))
  (local lines [])
  (each [line (pipe:lines)] (table.insert lines line))
  (pipe:close)
  lines))
(local read-file
  (fn [path]
  (local file (assert (io.open path "r")))
  (local content (file:read "*a"))
  (file:close)
  content))
(local elm-escape
  (fn [value]
  (var escaped (string.gsub value "\\" "\\\\"))
  (set escaped (string.gsub escaped "\"" "\\\""))
  (set escaped (string.gsub escaped "\n" "\\n"))
  (set escaped (string.gsub escaped "\r" "\\r"))
  (set escaped (string.gsub escaped "\t" "\\t"))
  escaped))
(local source-files
  (fun.totable
    (fun.filter
      (fn [path] (not (= path "")))
      (read-lines "git ls-files '*.agda' | LC_ALL=C sort"))))
(local nodes [])
(local edges [])
(each [_ path (ipairs source-files)]
  (local content (read-file path))
  (local module-name
    (string.gsub
      (string.gsub path "%.agda$" "")
      "/"
      "."))
  (local imports [])
  (each [_ line (ipairs content-lines)]
    (local imported
      (or
        (string.match line "^%s*open%s+import%s+([^%s]+)")
        (string.match line "^%s*import%s+([^%s]+)")))
    (when imported (table.insert imports imported)))
  (table.insert nodes {:id module-name :label module-name :source path})
  (each [_ imported (ipairs imports)]
    (table.insert edges {:source module-name :target imported :relation "imports"})))
(local rendered-nodes
  (fun.totable
    (fun.map
      (fn [node]
        (string.format "    { id = \"%s\", label = \"%s\", source = \"%s\" } ::"
          (elm-escape node.id) (elm-escape node.label) (elm-escape node.source)))
      nodes)))
(local rendered-edges
  (fun.totable
    (fun.map
      (fn [edge]
        (string.format "    { source = \"%s\", target = \"%s\", relation = \"%s\" } ::"
          (elm-escape edge.source) (elm-escape edge.target) (elm-escape edge.relation)))
      edges)))
(local output-path (assert (. arg 1) "usage: agda_graph.fnl OUTPUT.elm"))
(local output (assert (io.open output-path "w")))
(output:write "module GeneratedAgdaGraph exposing (Node, Edge, nodes, edges)\n\n")
(output:write "type alias Node = { id : String, label : String, source : String }\n")
(output:write "type alias Edge = { source : String, target : String, relation : String }\n\n")
(output:write "nodes : List Node\nnodes =\n")
(output:write (table.concat rendered-nodes "\n"))
(output:write "\n    []\n\nedges : List Edge\nedges =\n")
(output:write (table.concat rendered-edges "\n"))
(output:write "\n    []\n")
(output:close)
(print (.. "Generated Agda import graph: " output-path))
(print (.. "nodes=" (# nodes) " edges=" (# edges)))
