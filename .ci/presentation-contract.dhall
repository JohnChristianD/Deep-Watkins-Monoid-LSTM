{
  agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ],
  pageGenerator = ".ci/fennel/pages.fnl",
  pageTemplate = "index.html",
  lessStylesheet = "site/site.less",
  paletteCssGenerator = ".ci/fennel/palette_css.fnl",
  outputContract = "static HTML and CSS only; no browser JavaScript",
  interactiveSearch = False,
  interactiveFiltering = False,
  agdaJavaScriptBackend = False,
  graphSearch = False
}
