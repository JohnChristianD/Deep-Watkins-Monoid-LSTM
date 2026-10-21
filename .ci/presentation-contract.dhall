{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, monolithContentGenerator = ".ci/fennel/agda_graph.fnl"
, generatedContentModule = "monolith-content.mjs"
, nativePageModel = "FullCoupled.Agda2HsSemanticExtractor"
, compiledPageModel = "jAgda.FullCoupled.Agda2HsSemanticExtractor.mjs"
, buildRenderer = "site/app.mjs"
, siteEntry = "index.html"
, lessStylesheet = "site/site.less"
, compiledStylesheet = "site.css"
, paletteCssGenerator = ".ci/fennel/palette_css.fnl"
, paletteRoleRegistry = "site/site.less"
, outputContract = "static HTML and CSS only; no browser JavaScript"
, interactiveSearch = False
, interactiveFiltering = False
}
