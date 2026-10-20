module Main exposing (main)

import Browser
import GeneratedMonolithContent as Content
import GeneratedTheoremSurface as Surface
import Html exposing (Html, a, button, div, footer, h1, h2, h3, header, input, li, main_, nav, p, section, span, text, ul)
import Html
import Html.Attributes as HA
import Html.Events as HE
import List
import String


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



type FileFilter
    = AllFiles
    | LearnerOnly
    | TheoremOnly


type alias Model =
    { query : String
    , fileFilter : FileFilter
    , selected : Maybe String
    }


type Msg
    = SetQuery String
    | SetFileFilter String
    | SelectEntry String


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


farthestFrom : List Perceptual -> Perceptual -> List Perceptual -> Perceptual
farthestFrom chosen candidate candidates =
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
                candidates


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

            first :: rest ->
                let
                    next =
                        if List.isEmpty chosen then
                            first
                        else
                            farthestFrom chosen first rest
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
                , ";scroll-behavior:smooth;}"
                , "*{box-sizing:border-box;}"
                , "body{margin:0;background:"
                , perceptualCss paper
                , ";color:"
                , perceptualCss ink
                , ";font-family:'Atkinson Hyperlegible Mono','Iosevka',monospace;font-size:16px;line-height:1.55;}"
                , "button,input{font:inherit;}"
                , "a{color:inherit;text-underline-offset:.2em;text-decoration-thickness:.08em;}"
                , "a:hover{text-decoration-thickness:.15em;}"
                , "button,input{border:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 42%,transparent);background:transparent;color:inherit;border-radius:0;}"
                , "button:focus-visible,input:focus-visible,a:focus-visible{outline:2px solid "
                , perceptualCss accent
                , ";outline-offset:3px;}"
                , ".shell{min-height:100vh;max-width:88rem;margin:0 auto;padding:0 clamp(1rem,4vw,3rem);}"
                , ".masthead{display:flex;align-items:center;justify-content:space-between;gap:2rem;border-bottom:2px solid "
                , perceptualCss ink
                , ";padding:1.15rem 0 1rem;}"
                , ".brand{font-weight:700;letter-spacing:-.04em;font-size:1.15rem;}"
                , ".mast-note{margin:0;color:"
                , perceptualCss quiet
                , ";font-size:.78rem;max-width:54ch;text-align:right;}"
                , ".layout{display:grid;grid-template-columns:13rem minmax(0,1fr);gap:clamp(1.5rem,4vw,4.5rem);align-items:start;}"
                , ".side-nav{position:sticky;top:0;align-self:start;padding:2rem 0 1rem;}"
                , ".nav-title{font-size:.72rem;font-weight:700;letter-spacing:.13em;text-transform:uppercase;color:"
                , perceptualCss quiet
                , ";margin:0 0 .8rem;}"
                , ".nav-list{list-style:none;padding:0;margin:0 0 1.8rem;}"
                , ".nav-list li{border-top:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);}"
                , ".nav-list a{display:block;padding:.55rem 0;text-decoration:none;font-size:.82rem;overflow-wrap:anywhere;}"
                , ".nav-list a:hover{color:"
                , perceptualCss accent
                , ";text-decoration:underline;}"
                , ".source-link{display:block;border-left:3px solid "
                , perceptualCss accent
                , ";padding:.15rem 0 .15rem .7rem;margin:.55rem 0;font-size:.75rem;overflow-wrap:anywhere;}"
                , ".document{min-width:0;padding:2.3rem 0 3rem;max-width:76ch;}"
                , ".eyebrow{font-size:.68rem;letter-spacing:.14em;text-transform:uppercase;color:"
                , perceptualCss quiet
                , ";font-weight:700;}"
                , "h1{font-size:clamp(2rem,4.4vw,3.6rem);line-height:1.08;letter-spacing:-.06em;margin:.45rem 0 1.25rem;max-width:20ch;}"
                , "h2{font-size:1.35rem;line-height:1.25;letter-spacing:-.03em;margin:0 0 .8rem;}"
                , "h3{font-size:1rem;line-height:1.35;margin:.35rem 0;overflow-wrap:anywhere;}"
                , ".lede{font-size:1.06rem;line-height:1.6;max-width:66ch;margin:0 0 1.2rem;}"
                , ".intro{padding:0 0 2rem;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 28%,transparent);}"
                , ".stats{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:1rem;margin:1.6rem 0 0;}"
                , ".stat{border-top:2px solid "
                , perceptualCss accent
                , ";padding:.65rem 0 .4rem;}"
                , ".stat strong{display:block;font-size:1.45rem;line-height:1.2;}"
                , ".stat span{font-size:.69rem;letter-spacing:.08em;text-transform:uppercase;color:"
                , perceptualCss quiet
                , ";}"
                , ".section{padding:2rem 0;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 22%,transparent);scroll-margin-top:1rem;}"
                , ".section-lede{margin:.1rem 0 1.1rem;max-width:68ch;}"
                , ".source-record{padding:.85rem 0;border-top:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 16%,transparent);}"
                , ".source-record .source-path{display:block;font-size:.72rem;color:"
                , perceptualCss quiet
                , ";overflow-wrap:anywhere;margin-top:.35rem;}"
                , ".tools{display:grid;grid-template-columns:minmax(0,1fr);gap:.7rem;margin:1rem 0;}"
                , ".tools input{width:100%;padding:.7rem .75rem;border-radius:0;}"
                , ".filter-row{display:flex;flex-wrap:wrap;gap:.4rem;}"
                , ".filter-row button{padding:.45rem .7rem;font-size:.78rem;cursor:pointer;}"
                , ".filter-row button[data-active='true']{background:"
                , perceptualCss accent
                , ";color:"
                , perceptualCss inkOnAccent
                , ";}"
                , ".result-count{font-size:.76rem;color:"
                , perceptualCss quiet
                , ";margin:.5rem 0 1rem;}"
                , ".entry{padding:1rem 0;border-top:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 18%,transparent);}"
                , ".entry[data-selected='true']{border-top:2px solid "
                , perceptualCss accent
                , ";}"
                , ".entry-meta{display:flex;flex-wrap:wrap;align-items:center;gap:.6rem;font-size:.7rem;color:"
                , perceptualCss quiet
                , ";}"
                , ".entry-kind{font-weight:700;text-transform:uppercase;letter-spacing:.08em;}"
                , ".entry-select{border:0;padding:0;text-align:left;cursor:pointer;font-weight:700;overflow-wrap:anywhere;}"
                , ".entry-select:hover{color:"
                , perceptualCss accent
                , ";text-decoration:underline;}"
                , ".signature{font-size:.8rem;line-height:1.45;margin:.45rem 0;overflow-wrap:anywhere;white-space:pre-wrap;}"
                , ".detail{margin:.65rem 0 0;padding:.7rem 0 .15rem;border-top:1px dotted color-mix(in srgb,"
                , perceptualCss ink
                , " 28%,transparent);font-size:.78rem;}"
                , ".russ-note{border-left:3px solid "
                , perceptualCss accentTwo
                , ";padding:.4rem 0 .4rem 1rem;margin:1rem 0;}"
                , ".trust-label{display:inline-block;font-weight:700;letter-spacing:.05em;text-transform:uppercase;font-size:.68rem;color:"
                , perceptualCss accent
                , ";}"
                , ".palette{display:flex;gap:.35rem;flex-wrap:wrap;margin-top:1rem;}"
                , ".swatch{width:3.8rem;height:1.8rem;border:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 24%,transparent);}"
                , ".palette-caption{font-size:.75rem;color:"
                , perceptualCss quiet
                , ";margin:.5rem 0 0;}"
                , ".footer{padding:1.5rem 0 2.5rem;font-size:.72rem;line-height:1.5;color:"
                , perceptualCss quiet
                , ";}"
                , "@media(max-width:780px){.layout{grid-template-columns:minmax(0,1fr);gap:0}.masthead{align-items:flex-start;flex-direction:column;gap:.4rem}.mast-note{text-align:left}.side-nav{position:relative;padding:1rem 0;border-bottom:1px solid color-mix(in srgb,"
                , perceptualCss ink
                , " 22%,transparent)}.nav-list{display:flex;flex-wrap:wrap;gap:.3rem 1rem;margin-bottom:.7rem}.nav-list li{border:0}.nav-list a{padding:.2rem 0}.side-nav .nav-title{margin-top:.6rem}.document{padding-top:1.5rem}.stats{grid-template-columns:repeat(2,minmax(0,1fr));}}"
                ]
            )
        ]


init : Model
init =
    { query = ""
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


isLearnerEntry : Content.Entry -> Bool
isLearnerEntry entry =
    String.endsWith "CanonicalLearnerMonolith.agda" entry.source


filterMatches : FileFilter -> Content.Entry -> Bool
filterMatches filter entry =
    case filter of
        AllFiles ->
            True

        LearnerOnly ->
            isLearnerEntry entry

        TheoremOnly ->
            not (isLearnerEntry entry)


entryMatchesQuery : String -> Content.Entry -> Bool
entryMatchesQuery query entry =
    matches query (String.join " " [ entry.name, entry.signature, entry.source, entry.category ])


visibleEntries : Model -> List Content.Entry
visibleEntries model =
    List.filter
        (\entry ->
            filterMatches model.fileFilter entry
                && entryMatchesQuery model.query entry
        )
        Content.entries


selectedEntry : Model -> Maybe Content.Entry
selectedEntry model =
    case model.selected of
        Nothing ->
            Nothing

        Just identity ->
            Content.entries
                |> List.filter (\entry -> entry.id == identity)
                |> List.head


sourceUrl : Content.Entry -> String
sourceUrl entry =
    "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/fix/russ-audit-and-extraction-20261020/"
        ++ entry.source
        ++ "#L"
        ++ String.fromInt entry.line


sourceLabel : String -> String
sourceLabel path =
    if String.endsWith "CanonicalLearnerMonolith.agda" path then
        "Canonical learner semantics"

    else
        "Theorem and proof monolith"


sourceRecord : String -> Html Msg
sourceRecord path =
    let
        learner =
            String.endsWith "CanonicalLearnerMonolith.agda" path

        title =
            if learner then
                "Canonical learner monolith"

            else
                "Theorem monolith"

        summaryText =
            if learner then
                "Defines the coupled recurrent learner, state transitions, optimizer and policy semantics. Its named RUSS basis is the single declared source of recursive/computability assumptions."

            else
                "Contains theorem statements and proof constructions over the learner definitions. Reflection/TC primitives and imported theorem libraries are explicit trust boundaries, not automatic evidence of consistency."
    in
    div [ HA.class "source-record" ]
        [ h3 [] [ text title ]
        , p [] [ text summaryText ]
        , a
            [ HA.class "source-link"
            , HA.href
                ("https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/fix/russ-audit-and-extraction-20261020/"
                    ++ path
                )
            , HA.target "_blank"
            , HA.rel "noreferrer"
            ]
            [ text path ]
        ]


entryDetails : Content.Entry -> Html Msg
entryDetails entry =
    div [ HA.class "detail" ]
        [ p []
            [ text
                ("Source: "
                    ++ entry.source
                    ++ " at line "
                    ++ String.fromInt entry.line
                    ++ ". This entry is indexed from the monolith text; its presence here is not a type-checking or consistency claim."
                )
            ]
        , a
            [ HA.href (sourceUrl entry)
            , HA.target "_blank"
            , HA.rel "noreferrer"
            ]
            [ text "Open declaration in source" ]
        ]


entryCard : Model -> Content.Entry -> Html Msg
entryCard model entry =
    let
        selected =
            model.selected == Just entry.id
    in
    div
        [ HA.class "entry"
        , HA.attribute "data-selected" (if selected then "true" else "false")
        ]
        [ div [ HA.class "entry-meta" ]
            [ span [ HA.class "entry-kind" ] [ text entry.category ]
            , span [] [ text (entry.source ++ ":" ++ String.fromInt entry.line) ]
            ]
        , button
            [ HA.class "entry-select"
            , HE.onClick (SelectEntry entry.id)
            , HA.attribute "aria-expanded" (if selected then "true" else "false")
            ]
            [ h3 [] [ text entry.name ] ]
        , p [ HA.class "signature" ] [ text (if String.isEmpty entry.signature then "(signature continues below)" else entry.signature) ]
        , if selected then
            entryDetails entry

          else
            text ""
        ]


anchorLink : String -> String -> Html Msg
anchorLink label fragment =
    li [] [ a [ HA.href ("#" ++ fragment) ] [ text label ] ]


view : Model -> Html Msg
view model =
    let
        entries =
            visibleEntries model

        queryCount =
            List.length entries

        searchLimit =
            60

        selected =
            selectedEntry model

        russEntries =
            List.take 24 Surface.russEntryLines
    in
    main_ [ HA.class "shell" ]
        [ styleSheet
        , header [ HA.class "masthead" ]
            [ div [ HA.class "brand" ] [ text "The Monoid LSTM Project" ]
            , p [ HA.class "mast-note" ]
                [ text "A source-first technical index of the canonical learner and theorem monoliths." ]
            ]
        , div [ HA.class "layout" ]
            [ nav [ HA.class "side-nav" ]
                [ p [ HA.class "nav-title" ] [ text "Contents" ]
                , ul [ HA.class "nav-list" ]
                    [ anchorLink "Overview" "overview"
                    , anchorLink "Source files" "sources"
                    , anchorLink "Russian constructivism" "russ"
                    , anchorLink "Declaration index" "declarations"
                    , anchorLink "Perceptual palette" "palette"
                    ]
                , p [ HA.class "nav-title" ] [ text "Canonical files" ]
                , div []
                    (List.map
                        (\path ->
                            a
                                [ HA.class "source-link"
                                , HA.href
                                    ("https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/fix/russ-audit-and-extraction-20261020/"
                                        ++ path
                                    )
                                , HA.target "_blank"
                                , HA.rel "noreferrer"
                                ]
                                [ text (sourceLabel path) ]
                        )
                        Content.sourceFiles
                    )
                ]
            , div [ HA.class "document" ]
                [ section [ HA.id "overview", HA.class "intro" ]
                    [ div [ HA.class "eyebrow" ] [ text "Formal specification / proof surface" ]
                    , h1 [] [ text Surface.siteTitle ]
                    , p [ HA.class "lede" ]
                        [ text "Two monoliths define the public intellectual shape of this project: the learner's computational semantics, and the theorems built over those semantics. This index is regenerated from their actual declaration signatures; unrelated Agda modules are excluded from the page content." ]
                    , div [ HA.class "stats" ]
                        [ div [ HA.class "stat" ]
                            [ Html.strong [] [ text (String.fromInt Surface.learnerEntryCount) ]
                            , span [] [ text "learner entries" ]
                            ]
                        , div [ HA.class "stat" ]
                            [ Html.strong [] [ text (String.fromInt Surface.theoremEntryCount) ]
                            , span [] [ text "theorem entries" ]
                            ]
                        , div [ HA.class "stat" ]
                            [ Html.strong [] [ text (String.fromInt (List.length Content.entries)) ]
                            , span [] [ text "indexed declarations" ]
                            ]
                        ]
                    ]
                , section [ HA.id "sources", HA.class "section" ]
                    [ h2 [] [ text "The two canonical source files" ]
                    , p [ HA.class "section-lede" ] [ text "The learner monolith owns definitions and computational semantics. The theorem monolith owns proof constructions, theorem statements, and the explicit boundary between derived results and assumptions." ]
                    , div [] (List.map sourceRecord Content.sourceFiles)
                    ]
                , section [ HA.id "russ", HA.class "section" ]
                    [ h2 [] [ text "Russian constructivism (RUSS): trust-surface certificate" ]
                    , p [ HA.class "section-lede" ] [ text "The learner monolith packages three named RUSS assumptions in one record: Markov's principle for decidable predicates, register-machine ECT₀, and proposition-valued countable choice. The record makes these dependencies visible; it does not prove their joint consistency." ]
                    , div [ HA.class "russ-note" ]
                        [ span [ HA.class "trust-label" ] [ text "Audit boundary" ]
                        , p [] [ text "The theorem monolith also contains compiler-facing Agda Reflection / TC interfaces and imports external theorem libraries. This page can certify the declared source surface and configured non-cubical mode, but a text scan or failure to find an inhabitant of bottom cannot prove consistency of the whole theory or its transitive dependencies." ]
                        ]
                    , p [] [ text ("Indexed RUSS assumptions, postulates, and reflection trust entries: " ++ String.fromInt (List.length Surface.russEntryLines)) ]
                    , div [] (List.map (\line -> p [ HA.class "signature" ] [ text line ]) russEntries)
                    ]
                , section [ HA.id "declarations", HA.class "section" ]
                    [ h2 [] [ text "Declaration index" ]
                    , p [ HA.class "section-lede" ] [ text "Search by identifier, type signature, source file, or classification. Choose an entry to reveal its source-line link. The index follows monolith edits at build time." ]
                    , div [ HA.class "tools" ]
                        [ input
                            [ HA.attribute "aria-label" "Search monolith declarations"
                            , HA.placeholder "Search names, signatures, or categories"
                            , HA.value model.query
                            , HE.onInput SetQuery
                            ]
                            []
                        , div [ HA.class "filter-row" ]
                            [ button
                                [ HE.onClick (SetFileFilter "all")
                                , HA.attribute "data-active" (if model.fileFilter == AllFiles then "true" else "false")
                                ]
                                [ text "Both monoliths" ]
                            , button
                                [ HE.onClick (SetFileFilter "learner")
                                , HA.attribute "data-active" (if model.fileFilter == LearnerOnly then "true" else "false")
                                ]
                                [ text "Learner only" ]
                            , button
                                [ HE.onClick (SetFileFilter "theorem")
                                , HA.attribute "data-active" (if model.fileFilter == TheoremOnly then "true" else "false")
                                ]
                                [ text "Theorems only" ]
                            ]
                        ]
                    , p [ HA.class "result-count" ]
                        [ text
                            ("Showing "
                                ++ String.fromInt (min searchLimit queryCount)
                                ++ " of "
                                ++ String.fromInt queryCount
                                ++ " matches. Select a declaration to inspect its source location."
                            )
                        ]
                    , div [] (List.map (entryCard model) (List.take searchLimit entries))
                    ]
                , section [ HA.id "palette", HA.class "section" ]
                    [ h2 [] [ text "Maximin perceptual palette" ]
                    , p [ HA.class "section-lede" ] [ text "The palette remains selected by farthest-point maximin spacing over the existing CAT02LMS-derived opponent coordinates. The layout changed; the color transform and selection algorithm did not." ]
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
                    , p [ HA.class "palette-caption" ]
                        [ text ("CAT02LMS / " ++ String.fromInt (List.length maximinPalette) ++ " maximin colors. Palette values are computed in Elm.") ]
                    ]
                , footer [ HA.class "footer" ]
                    [ text
                        ("Source scope: "
                            ++ String.join " • " Content.sourceFiles
                            ++ ". "
                            ++ String.fromInt (List.length Content.entries)
                            ++ " signature-shaped declarations were extracted into this index. It is a reader and audit aid, not a substitute for Agda type-checking."
                        )
                    ]
                ]
            ]
        ]


update : Msg -> Model -> Model
update msg model =
    case msg of
        SetQuery value ->
            { model | query = value }

        SetFileFilter value ->
            { model | fileFilter = setFilter value }

        SelectEntry value ->
            { model | selected = if model.selected == Just value then Nothing else Just value }


main : Program () Model Msg
main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }
