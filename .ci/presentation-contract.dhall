{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, monolithContentGenerator = ".ci/fennel/monolith_catalog.fnl"
, generatedContentModule = "monolith-content.mjs"
, pureRenderer = "site/render.mjs"
, immutablePageModel = "site/page-model.mjs"
, buildIoAdapter = "site/app.mjs"
, siteEntry = "index.html"
, lessStylesheet = "site/site.less"
, compiledStylesheet = "site.css"
, paletteCssGenerator = ".ci/fennel/palette_css.fnl"
, paletteRoleRegistry = "site/site.less"
, outputContract = "static HTML and CSS only; no browser JavaScript"
, interactiveSearch = False
, interactiveFiltering = False
}
