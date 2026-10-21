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


paletteCandidateCount : Int
paletteCandidateCount =
    sitePaletteSize * sitePaletteSize



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
    | SetFileFilter FileFilter
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

        extra =
            index - 90

        hue =
            if index < 90 then
                tau * toFloat (modBy 18 index) / 18
            else
                tau * toFloat (modBy 720 extra) / 720

        light =
            if index < 90 then
                0.28 + 0.045 * toFloat (modBy 5 index)
            else
                0.18 + 0.0005 * toFloat (modBy 100 extra)

        chroma =
            0.34
    in
    { r = clamp01 (light + chroma * cos hue)
    , g = clamp01 (light + chroma * cos (hue - 2.0943951023931953))
    , b = clamp01 (light + chroma * cos (hue + 2.0943951023931953))
    }


candidateColors : List Perceptual
candidateColors =
    List.map (candidateRgb >> cat02LmsToOpponent) (List.range 0 (paletteCandidateCount - 1))


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
    maximinStep (List.length candidateColors) candidateColors []


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
        |> List.drop (modBy (List.length maximinPalette) index)
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
                [ ":root{--palette-ink:"
                , perceptualCss ink
                , ";--palette-paper:"
                , perceptualCss paper
                , ";--palette-accent:"
                , perceptualCss accent
                , ";--palette-accent-two:"
                , perceptualCss accentTwo
                , ";--palette-quiet:"
                , perceptualCss quiet
                , ";--palette-ink-on-accent:"
                , perceptualCss inkOnAccent
                , ";}"
                ]
            )
        ]


init : Model
init =
    { query = ""
    , fileFilter = AllFiles
    , selected = Nothing
    }


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
    List.any (matches query) [ entry.name, entry.signature, entry.source, entry.category ]


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
    "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/"
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
                ("https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/"
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
                [ text "GNU.org-inspired, source-first index. Content is derived only from the canonical learner and theorem monoliths." ]
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
                , a [ HA.href "https://www.gnu.org/", HA.target "_blank", HA.rel "noreferrer", HA.class "source-link" ] [ text "GNU.org · free software and formal tools" ]
                , p [ HA.class "nav-title" ] [ text "Canonical files" ]
                , div []
                    (List.map
                        (\path ->
                            a
                                [ HA.class "source-link"
                                , HA.href
                                    ("https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/"
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
                                [ HE.onClick (SetFileFilter AllFiles)
                                , HA.attribute "data-active" (if model.fileFilter == AllFiles then "true" else "false")
                                ]
                                [ text "Both monoliths" ]
                            , button
                                [ HE.onClick (SetFileFilter LearnerOnly)
                                , HA.attribute "data-active" (if model.fileFilter == LearnerOnly then "true" else "false")
                                ]
                                [ text "Learner only" ]
                            , button
                                [ HE.onClick (SetFileFilter TheoremOnly)
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

        SetFileFilter filter ->
            { model | fileFilter = filter }

        SelectEntry value ->
            { model | selected = if model.selected == Just value then Nothing else Just value }


main : Program () Model Msg
main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }
