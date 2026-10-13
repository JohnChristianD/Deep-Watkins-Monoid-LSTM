{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, graphGenerator = ".ci/lua/agda_graph.fnl"
, surfaceGenerator = ".ci/lua/agda_surface.fnl"
, elmManifest = ".ci/elm-application.dhall"
, siteEntry = "index.html"
, compiledElm = "elm.js"
, asciiGenerator = ".ci/lua/ascii_surface.fnl"
}
