{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, monolithContentGenerator = ".ci/fennel/agda_graph.fnl"
, generatedContentScript = "monolith-content.js"
, nativeSearchModule = "FullCoupled.Agda2HsSemanticExtractor"
, compiledSearchModule = "jAgda.FullCoupled.Agda2HsSemanticExtractor.mjs"
, browserRuntime = "site/app.mjs"
, siteEntry = "index.html"
, lessStylesheet = "site/site.less"
, compiledStylesheet = "site.css"
, paletteCssGenerator = ".ci/fennel/palette_css.fnl"
, paletteRoleRegistry = "site/site.less"
, asciiGenerator = ".ci/fennel/ascii_surface.fnl"
}
