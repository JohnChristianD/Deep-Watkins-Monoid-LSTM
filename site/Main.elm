module Main exposing (main)

import Browser
import Char
import GeneratedAgdaGraph as Graph
import GeneratedTheoremSurface as Surface
import Html exposing (Html, button, div, h1, h2, header, input, li, main_, nav, p, section, span, text, ul)
import Html
import Html.Attributes as HA
import Html.Events as HE
import List
import String
import Svg as S
import Svg.Attributes as SA


type alias Rgb =
    { r : Float
    , g : Float
    , b : Float
    }


type alias Perceptual =
    { rgb : Rgb
    , l : Float
    , a : Float
    , b : Float
    }


type FileFilter
    = AllFiles
    | LearnerOnly
    | TheoremOnly


type PaletteRole
    = InkRole
    | PaperRole
    | AccentRole
    | AccentTwoRole
    | QuietRole
    | InkOnAccentRole


sitePaletteRoles : List PaletteRole
sitePaletteRoles =
    [ InkRole
    , PaperRole
    , AccentRole
    , AccentTwoRole
    , QuietRole
    , InkOnAccentRole
    ]


paletteIndex : PaletteRole -> Int
paletteIndex role =
    case role of
        InkRole ->
            0

        PaperRole ->
            1

        AccentRole ->
            2

        AccentTwoRole ->
            3

        QuietRole ->
            4

        InkOnAccentRole ->
            5


sitePaletteSize : Int
sitePaletteSize =
    List.length sitePaletteRoles


type alias Model =
    { query : String
    , relationQuery : String
    , fileFilter : FileFilter
    , selected : Maybe String
    }


type Msg
    = SetQuery String
    | SetRelationQuery String
    | SetFileFilter String
    | SelectNode String


clamp01 : Float -> Float
clamp01 value =
    max 0 (min 1 value)


cat02Lms : Rgb -> ( Float, Float, Float )
cat02Lms color =
    ( 0.7328 * color.r + 0.4296 * color.g - 0.1624 * color.b
    , -0.7036 * color.r + 1.6975 * color.g + 0.0061 * color.b
    , 0.0030 * color.r + 0.0136 * color.g + 0.9834 * color.b
    )


cat02LmsToOpponent : Rgb -> Perceptual
cat02LmsToOpponent rgb =
    let
        ( l, m, s ) =
            cat02Lms rgb
    in
    { rgb = rgb
    , l = (l + m + s) / 1.7320508075688772
    , a = (l - m) / 1.4142135623730951
    , b = (l + m - 2 * s) / 2.449489742783178
    }


distanceSquared : Perceptual -> Perceptual -> Float
distanceSquared left right =
    let
        dl =
            left.l - right.l

        da =
            left.a - right.a

        db =
            left.b - right.b
    in
    dl * dl + da * da + db * db


candidateRgb : Int -> Rgb
candidateRgb index =
    let
        tau =
            6.283185307179586

        hue =
            tau * toFloat (modBy 18 index) / 18

        light =
            0.28 + 0.045 * toFloat (modBy 5 index)

        chroma =
            0.34
    in
    { r = clamp01 (light + chroma * cos hue)
    , g = clamp01 (light + chroma * cos (hue - 2.0943951023931953))
    , b = clamp01 (light + chroma * cos (hue + 2.0943951023931953))
    }


candidateColors : List Perceptual
candidateColors =
    List.map (candidateRgb >> cat02LmsToOpponent) (List.range 0 35)


farthestFrom : List Perceptual -> Perceptual -> Perceptual
farthestFrom chosen candidate =
    case chosen of
        [] ->
            candidate

        _ ->
            List.foldl
                (\item best ->
                    if minimumDistance chosen item > minimumDistance chosen best then
                        item
                    else
                        best
                )
                candidate
                candidateColors


minimumDistance : List Perceptual -> Perceptual -> Float
minimumDistance chosen candidate =
    case chosen of
        [] ->
            1 / 0

        first :: rest ->
            List.foldl
                (\item best -> min best (distanceSquared item candidate))
                (distanceSquared first candidate)
                rest


maximinStep : Int -> List Perceptual -> List Perceptual -> List Perceptual
maximinStep remaining candidates chosen =
    if remaining <= 0 then
        chosen

    else
        case candidates of
            [] ->
                chosen

            first :: _ ->
                let
                    next =
                        if List.isEmpty chosen then
                            first
                        else
                            farthestFrom chosen first
                in
                maximinStep
                    (remaining - 1)
                    (List.filter (\item -> distanceSquared item next > 0) candidates)
                    (chosen ++ [ next ])


maximinPalette : List Perceptual
maximinPalette =
    maximinStep sitePaletteSize candidateColors []


rgbCss : Rgb -> String
rgbCss color =
    "rgb("
        ++ String.fromInt (round (255 * clamp01 color.r))
        ++ " "
        ++ String.fromInt (round (255 * clamp01 color.g))
        ++ " "
        ++ String.fromInt (round (255 * clamp01 color.b))
        ++ ")"


perceptualCss : Perceptual -> String
perceptualCss color =
    rgbCss color.rgb


paletteAt : Int -> Perceptual
paletteAt index =
    maximinPalette
        |> List.drop (modBy sitePaletteSize index)
        |> List.head
        |> Maybe.withDefault (cat02LmsToOpponent (candidateRgb 0))


paletteFor : PaletteRole -> Perceptual
paletteFor role =
    paletteAt (paletteIndex role)


ink : Perceptual
ink =
    paletteFor InkRole


paper : Perceptual
paper =
    paletteFor PaperRole


accent : Perceptual
accent =
    paletteFor AccentRole


accentTwo : Perceptual
accentTwo =
    paletteFor AccentTwoRole


quiet : Perceptual
quiet =
    paletteFor QuietRole


inkOnAccent : Perceptual
inkOnAccent =
    paletteFor InkOnAccentRole


styleSheet : Html msg
styleSheet =
    Html.node "style" []
        [ text
            (String.join ""
                [ "@import url('https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible+Mono:wght@400;700&display=swap');"
                , ":root{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;background:"
                , perceptualCss paper
                , ";color:"
                , perceptualCss ink
                , ";}"
                , "*{box-sizing:border-box;}"
                , "body{margin:0;background:"
                , perceptualCss paper
                , ";color:"
                , perceptualCss ink
                , ";font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;}"
                , "button,input{font:inherit;}"
                , "button,input,select{border:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 42%,transparent);background:transparent;color:inherit;}"
                , "button:focus-visible,input:focus-visible{outline:2px solid "
                , perceptualCss accent
                , ";outline-offset:3px;}"
                , ".shell{min-height:100vh;display:grid;grid-template-columns:minmax(13rem,18rem) minmax(0,1fr);max-width:92rem;margin:0 auto;}"
                , ".rail{position:sticky;top:0;height:100vh;overflow:auto;padding:1.5rem 1.25rem;border-right:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);}"
                , ".brand{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-weight:700;letter-spacing:-.04em;font-size:1.05rem;margin-bottom:1.5rem;}"
                , ".eyebrow{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.68rem;letter-spacing:.16em;text-transform:uppercase;color:"
                , perceptualCss quiet
                , ";}"
                , ".module-list{list-style:none;padding:0;margin:1rem 0;display:grid;gap:.25rem;}"
                , ".module-list button{width:100%;min-width:0;text-align:left;padding:.55rem .65rem;border-radius:.2rem;cursor:pointer;overflow-wrap:anywhere;}"
                , ".module-list button:hover,.module-list button[data-selected='true']{background:"
                , perceptualCss accent
                , ";color:"
                , perceptualCss inkOnAccent
                , ";}"
                , ".main{min-width:0;padding:clamp(1.5rem,4vw,4rem);}"
                , ".mast{display:block;max-width:70ch;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 22%,transparent);padding-bottom:1.4rem;margin-bottom:2.5rem;}"
                , "h1{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:clamp(2.1rem,5vw,4.2rem);line-height:1;letter-spacing:-.055em;margin:.35rem 0 1rem;max-width:18ch;}"
                , "h2{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:1.1rem;line-height:1.3;letter-spacing:-.025em;margin:0 0 .8rem;}"
                , ".lede{font-size:1.05rem;line-height:1.45;max-width:68ch;margin:0;}"
                , ".stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(11rem,1fr));gap:.75rem;max-width:70ch;margin-top:1.5rem;}"
                , ".stat{padding:.8rem 0;border-top:2px solid "
                , perceptualCss accent
                , ";background:color-mix(in srgb,"
                , perceptualCss accent
                , " 8%,transparent);}"
                , ".stat strong{display:block;font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:1.25rem;line-height:1.2;}"
                , ".tools{display:flex;gap:.5rem;flex-wrap:wrap;margin:1rem 0 1.5rem;}"
                , ".tools input,.tools button{padding:.65rem .75rem;border-radius:.2rem;}"
                , ".tools input{min-width:min(30rem,100%);flex:1;}"
                , ".section{max-width:70ch;margin:3.25rem 0;}"
                , ".records{display:block;}"
                , ".record{border-top:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);padding:1rem 0;background:transparent;}"
                , ".record:hover{border-color:"
                , perceptualCss accent
                , ";}"
                , ".record .kind{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.67rem;letter-spacing:.14em;text-transform:uppercase;color:"
                , perceptualCss quiet
                , ";}"
                , ".record h3{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.95rem;overflow-wrap:anywhere;margin:.45rem 0;}"
                , ".record p{margin:.45rem 0;line-height:1.45;max-width:70ch;}"
                , ".source{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.72rem;line-height:1.35;color:"
                , perceptualCss quiet
                , ";overflow-wrap:anywhere;}"
                , ".map{border-top:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);background:transparent;padding:1rem 0;overflow:auto;}"
                , ".map svg{display:block;width:100%;min-width:38rem;height:22rem;}"
                , ".relation{display:grid;grid-template-columns:minmax(0,1fr) minmax(7rem,9rem) minmax(0,1fr);gap:.75rem;align-items:center;padding:.7rem 0;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 12%,transparent);font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.75rem;}"
                , ".relation-end{min-width:0;overflow-wrap:anywhere;}"
                , ".relation-middle{min-width:7rem;text-align:center;display:flex;flex-direction:column;align-items:center;gap:.25rem;overflow-wrap:anywhere;}"
                , ".relation-kind{font-size:.62rem;line-height:1.2;letter-spacing:.04em;}"
                , ".arrow{line-height:1;color:"
                , perceptualCss accentTwo
                , ";}"
                , ".palette{display:flex;gap:.35rem;flex-wrap:wrap;max-width:70ch;}"
                , ".swatch{width:4rem;height:2rem;border:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 20%,transparent);}"
                , ".footer{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.68rem;line-height:1.4;color:"
                , perceptualCss quiet
                , ";margin-top:4rem;}"
                , "body{font-size:16px;line-height:1.4;}p,li{max-width:70ch;}strong{font-weight:700;}em{font-style:italic;}code,pre{font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:.86em;}a{color:inherit;text-underline-offset:.16em;}a:hover{text-decoration-thickness:2px;}@media(max-width:800px){.shell{display:block}.rail{position:relative;height:auto;border-right:0;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);overflow-x:hidden;}.module-list{grid-template-columns:minmax(0,1fr);}.module-list button{min-width:0;overflow-wrap:anywhere;}.mast{grid-template-columns:1fr}.main{padding:1rem;overflow-x:hidden}.map{overflow-x:auto}.map svg{min-width:30rem}}"
                ]
            )
        ]


init : Model
init =
    { query = ""
    , relationQuery = ""
    , fileFilter = AllFiles
    , selected = Nothing
    }


filterString : FileFilter -> String
filterString filter =
    case filter of
        AllFiles ->
            "all"

        LearnerOnly ->
            "learner"

        TheoremOnly ->
            "theorem"


setFilter : String -> FileFilter
setFilter value =
    case value of
        "learner" ->
            LearnerOnly

        "theorem" ->
            TheoremOnly

        _ ->
            AllFiles


matches : String -> String -> Bool
matches query value =
    String.isEmpty query || String.contains (String.toLower query) (String.toLower value)


visibleNodes : Model -> List Graph.Node
visibleNodes model =
    List.filter
        (\node ->
            let
                filterMatch =
                    case model.fileFilter of
                        AllFiles ->
                            True

                        LearnerOnly ->
                            String.contains "CanonicalLearner" node.source

                        TheoremOnly ->
                            String.contains "TheoremsMonolith" node.source
            in
            filterMatch
                && (matches model.query node.id || matches model.query node.source)
        )
        Graph.nodes


visibleEdges : Model -> List Graph.Edge
visibleEdges model =
    List.filter
        (\edge ->
            matches model.relationQuery edge.source
                || matches model.relationQuery edge.target
                || matches model.relationQuery edge.relation
        )
        Graph.edges


nodeColor : Int -> Perceptual
nodeColor index =
    paletteAt index


nodeCard : Model -> Int -> Graph.Node -> Html Msg
nodeCard model index node =
    let
        selected =
            model.selected == Just node.id

        color =
            nodeColor index
    in
    button
        [ HA.attribute "data-module" node.id
        , HA.attribute "data-selected" (if selected then "true" else "false")
        , HA.class "record"
        , HE.onClick (SelectNode node.id)
        ]
        [ span [ HA.class "kind" ] [ text "module" ]
        , h2 [] [ text node.label ]
        , p [ HA.class "source" ] [ text node.source ]
        ]


nodeOptions : Model -> Html Msg
nodeOptions model =
    nav [ HA.class "rail" ]
        [ div [ HA.class "brand" ] [ text "Agda / Mirth" ]
        , div [ HA.class "eyebrow" ] [ text "generated surface" ]
        , p [] [ text "A navigable proof surface, synchronized from the Agda dependency graph." ]
        , ul [ HA.class "module-list" ]
            (List.indexedMap
                (\index node ->
                    li []
                        [ button
                            [ HA.attribute "data-module" node.id
                            , HA.attribute "data-selected"
                                (if model.selected == Just node.id then "true" else "false")
                            , HE.onClick (SelectNode node.id)
                            ]
                            [ text (String.fromInt (index + 1) ++ "  " ++ node.label) ]
                        ]
                )
                (List.take 40 (visibleNodes model))
            )
        ]


graphView : Model -> Html Msg
graphView model =
    let
        nodes =
            List.take 18 (visibleNodes model)

        positions =
            List.indexedMap
                (\index node ->
                    let
                        x =
                            40 + toFloat (modBy 6 index) * 145

                        y =
                            35 + toFloat (index // 6) * 95
                    in
                    ( node, x, y )
                )
                nodes

        nodeCircle ( node, x, y ) =
            let
                color =
                    nodeColor (String.length node.id)
            in
            S.g []
                [ S.circle
                    [ SA.cx (String.fromFloat x)
                    , SA.cy (String.fromFloat y)
                    , SA.r "19"
                    , SA.fill (perceptualCss color)
                    , SA.stroke (perceptualCss ink)
                    , SA.strokeWidth "1"
                    ]
                    []
                , S.text_
                    [ SA.x (String.fromFloat x)
                    , SA.y (String.fromFloat (y + 3))
                    , SA.textAnchor "middle"
                    , SA.fontFamily "Atkinson Hyperlegible Mono, Iosevka, monospace"
                    , SA.fontSize "7"
                    , SA.fill (perceptualCss paper)
                    ]
                    [ S.text (String.fromInt (modBy 100 (indexForNode node.id))) ]
                ]

        edgeLines =
            List.take 28 (visibleEdges model)
                |> List.indexedMap
                    (\index edge ->
                        let
                            from =
                                positionFor edge.source positions

                            to =
                                positionFor edge.target positions
                        in
                        case ( from, to ) of
                            ( Just ( x1, y1 ), Just ( x2, y2 ) ) ->
                                S.line
                                    [ SA.x1 (String.fromFloat x1)
                                    , SA.y1 (String.fromFloat y1)
                                    , SA.x2 (String.fromFloat x2)
                                    , SA.y2 (String.fromFloat y2)
                                    , SA.stroke (perceptualCss accentTwo)
                                    , SA.strokeOpacity "0.45"
                                    ]
                                    []

                            _ ->
                                S.g [] []
                    )
    in
    div [ HA.class "map" ]
        [ S.svg
            [ SA.viewBox "0 0 820 330"
            , HA.attribute "role" "img"
            , HA.attribute "aria-label" "Agda module dependency map"
            ]
            (edgeLines ++ List.map nodeCircle positions)
        ]


indexForNode : String -> Int
indexForNode value =
    String.foldl (\char total -> total + Char.toCode char) 0 value


positionFor : String -> List ( Graph.Node, Float, Float ) -> Maybe ( Float, Float )
positionFor id positions =
    positions
        |> List.filter (\( node, _, _ ) -> node.id == id)
        |> List.head
        |> Maybe.map (\( _, x, y ) -> ( x, y ))


relationRecord : Graph.Edge -> Html Msg
relationRecord edge =
    div [ HA.class "relation" ]
        [ span [ HA.class "relation-end" ] [ text edge.source ]
        , div [ HA.class "relation-middle" ]
            [ span [ HA.class "relation-kind" ] [ text edge.relation ]
            , span
                [ HA.class "arrow"
                , HA.attribute "aria-hidden" "true"
                ]
                [ text "\u{2192}" ]
            ]
        , span [ HA.class "relation-end" ] [ text edge.target ]
        ]


view : Model -> Html Msg
view model =
    let
        nodes =
            visibleNodes model

        edges =
            visibleEdges model

        titleText =
            Surface.siteTitle

        selectedSource =
            case model.selected of
                Nothing ->
                    "Select a module to inspect its generated dependency neighborhood."

                Just value ->
                    value
    in
    main_ [ HA.class "shell" ]
        [ styleSheet
        , nodeOptions model
        , div [ HA.class "main" ]
            [ header [ HA.class "mast" ]
                [ div []
                    [ div [ HA.class "eyebrow" ] [ text "Type-theoretic dependency atlas" ]
                    , h1 [] [ text titleText ]
                    , p [ HA.class "lede" ]
                        [ text "A pure Elm reading surface for the synchronized Agda core: modules, imports, theorem edges, and the Mirth-generated projection." ]
                    ]
                , div [ HA.class "stats" ]
                    [ div [ HA.class "stat" ] [ span [ HA.class "eyebrow" ] [ text "modules" ], Html.strong [] [ text (String.fromInt (List.length Graph.nodes)) ] ]
                    , div [ HA.class "stat" ] [ span [ HA.class "eyebrow" ] [ text "relations" ], Html.strong [] [ text (String.fromInt (List.length Graph.edges)) ] ]
                    , div [ HA.class "stat" ] [ span [ HA.class "eyebrow" ] [ text "surface" ], Html.strong [] [ text "Mirth" ] ]
                    , div [ HA.class "stat" ] [ span [ HA.class "eyebrow" ] [ text "palette" ], Html.strong [] [ text "CAT02LMS" ] ]
                    ]
                ]
            , div [ HA.class "tools" ]
                [ input
                    [ HA.attribute "aria-label" "Search modules"
                    , HA.placeholder "search module or source"
                    , HA.value model.query
                    , HE.onInput SetQuery
                    ]
                    []
                , input
                    [ HA.attribute "aria-label" "Filter relations"
                    , HA.placeholder "filter relations"
                    , HA.value model.relationQuery
                    , HE.onInput SetRelationQuery
                    ]
                    []
                , button [ HE.onClick (SetFileFilter "all") ] [ text "all" ]
                , button [ HE.onClick (SetFileFilter "learner") ] [ text "learner" ]
                , button [ HE.onClick (SetFileFilter "theorem") ] [ text "theorem" ]
                ]
            , section [ HA.class "section" ]
                [ h2 [] [ text ("Modules / " ++ String.fromInt (List.length nodes)) ]
                , div [ HA.class "records" ] (List.indexedMap (nodeCard model) (List.take 48 nodes))
                ]
            , section [ HA.class "section" ]
                [ h2 [] [ text "Dependency map" ]
                , p [] [ text selectedSource ]
                , graphView model
                ]
            , section [ HA.class "section" ]
                [ h2 [] [ text ("Relations / " ++ String.fromInt (List.length edges)) ]
                , div [] (List.map relationRecord (List.take 120 edges))
                ]
            , section [ HA.class "section" ]
                [ h2 [] [ text "Maximin perceptual palette" ]
                , p [] [ text "Candidate colors are scored in a CAT02LMS-derived opponent space and selected by farthest-point maximin spacing." ]
                , div [ HA.class "palette" ]
                    (List.indexedMap
                        (\index color ->
                            div
                                [ HA.class "swatch"
                                , HA.attribute "title" ("maximin-" ++ String.fromInt (index + 1))
                                , HA.attribute "style" ("background:" ++ perceptualCss color)
                                ]
                                []
                        )
                        maximinPalette
                    )
                ]
            , p [ HA.class "footer" ]
                [ text
                    ("sources: "
                        ++ String.join ", " Surface.sourceFiles
                        ++ " | "
                        ++ String.fromInt (List.length Surface.nodeLines)
                        ++ " generated node lines | "
                        ++ String.fromInt (List.length Surface.edgeLines)
                        ++ " generated edge lines"
                    )
                ]
            ]
        ]


update : Msg -> Model -> Model
update msg model =
    case msg of
        SetQuery value ->
            { model | query = value }

        SetRelationQuery value ->
            { model | relationQuery = value }

        SetFileFilter value ->
            { model | fileFilter = setFilter value }

        SelectNode value ->
            { model | selected = Just value }


main : Program () Model Msg
main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }
