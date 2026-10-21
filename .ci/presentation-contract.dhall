{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, monolithContentGenerator = ".ci/fennel/agda_graph.fnl"
, surfaceGenerator = ".ci/fennel/agda_surface.fnl"
, elmManifest = ".ci/elm-application.dhall"
, siteEntry = "index.html"
, lessStylesheet = "site/site.less"
, compiledStylesheet = "site.css"
, paletteRuntime = "site/palette.js"
, compiledElm = "elm.js"
, asciiGenerator = ".ci/fennel/ascii_surface.fnl"
}
