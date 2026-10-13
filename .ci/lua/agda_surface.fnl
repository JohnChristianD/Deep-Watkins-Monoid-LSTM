(local output-path (assert (. arg 1) "usage: agda_surface.fnl OUTPUT.elm"))
(local output (assert (io.open output-path "w")))
(local source [[module GeneratedTheoremSurface exposing (siteTitle, sourceFiles, nodeLines, edgeLines, asciiSanitize)

import Char
import GeneratedAgdaGraph as Graph
import String

siteTitle : String
siteTitle =
    case Graph.nodes of
        first :: _ ->
            first.source

        [] ->
            "AgdaGraph"

sourceFiles : List String
sourceFiles =
    unique (List.map .source Graph.nodes)

unique : List String -> List String
unique values =
    uniqueHelp values []

uniqueHelp : List String -> List String -> List String
uniqueHelp values seen =
    case values of
        [] ->
            seen

        value :: rest ->
            if List.member value seen then
                uniqueHelp rest seen

            else
                uniqueHelp rest (seen ++ [ value ])

sanitizeChar : Char -> Char
sanitizeChar char =
    if Char.toCode char < 128 then
        char

    else
        Char.fromCode 63

asciiSanitize : String -> String
asciiSanitize value =
    String.map sanitizeChar value

nodeLine : Graph.Node -> String
nodeLine node =
    asciiSanitize (node.source ++ ":" ++ node.label)

nodeLines : List String
nodeLines =
    List.map nodeLine Graph.nodes

edgeLine : Graph.Edge -> String
edgeLine edge =
    asciiSanitize
        (edge.source
            ++ " --"
            ++ edge.relation
            ++ "--> "
            ++ edge.target
        )

edgeLines : List String
edgeLines =
    List.map edgeLine Graph.edges
]])
(output:write source)
(output:close)
(print (.. "Generated theorem surface: " output-path))
