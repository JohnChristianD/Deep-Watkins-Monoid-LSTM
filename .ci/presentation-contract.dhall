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
, wasmPaletteSource = ".ci/wasm/maximin_palette.c"
, compiledWasm = "site-palette.wasm"
, paletteLoader = "site/palette-loader.js"
, compiledElm = "elm.js"
, asciiGenerator = ".ci/fennel/ascii_surface.fnl"
}
