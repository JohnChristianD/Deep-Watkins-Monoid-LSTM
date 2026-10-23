const escapeHtml = (value) =>
  String(value).replace(/[&<>"']/g, (character) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
    "'": "&#39;"
  })[character]);

const exactSources = Object.freeze([
  "FullCoupled/CanonicalLearnerMonolith.agda",
  "FullCoupled/TheoremsMonolith.agda"
]);

const sourceUrl = (entry) =>
  "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" +
  entry.source + "#L" + entry.line;

export const renderStaticPage = (catalog, page, template) => {
  if (!catalog ||
      !Object.isFrozen(catalog) ||
      !Object.isFrozen(catalog.sourceFiles) ||
      !Object.isFrozen(catalog.entries) ||
      !catalog.entries.every(Object.isFrozen)) {
    throw new Error("catalog must be deeply frozen data");
  }
  if (catalog.sourceFiles.length !== exactSources.length ||
      catalog.sourceFiles.some((source, index) => source !== exactSources[index])) {
    throw new Error("Pages may index only the two canonical Agda monoliths");
  }
  if (!page ||
      !Object.isFrozen(page) ||
      typeof page.title !== "string" ||
      typeof page.overview !== "string" ||
      typeof page.consistencyStatus !== "string" ||
      typeof page.russTrustBoundary !== "string") {
    throw new Error("immutable page model is missing required fields");
  }
  if (typeof template !== "string" ||
      !template.includes("<!-- GENERATED_CONTENT -->")) {
    throw new Error("HTML template must contain the generated-content marker");
  }

  const labelFor = (source) =>
    source === exactSources[0] ? page.learnerLabel : page.theoremLabel;

  const sourceCards = catalog.sourceFiles.map((source) =>
    "<article class=\"source-record\">\n" +
    "  <h3>" + escapeHtml(labelFor(source)) + "</h3>\n" +
    "  <p><code>" + escapeHtml(source) + "</code></p>\n" +
    "  <p><a href=\"https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" +
    escapeHtml(source) + "\">Read canonical source</a></p>\n" +
    "</article>"
  ).join("\n");

  const declarationIndex = catalog.entries.map((entry) =>
    "<article class=\"entry\">\n" +
    "  <h3>" + escapeHtml(entry.name) + "</h3>\n" +
    "  <p class=\"signature\">" +
      escapeHtml(entry.signature || "(signature continues in source)") + "</p>\n" +
    "  <p class=\"entry-meta\">" + escapeHtml(entry.category) + " | " +
      escapeHtml(entry.source) + ":" + entry.line + "</p>\n" +
    "  <p><a href=\"" + escapeHtml(sourceUrl(entry)) +
      "\">Open declaration in source</a></p>\n" +
    "</article>"
  ).join("\n");

  const body =
    "<main class=\"shell\">\n" +
    "  <header class=\"masthead\">\n" +
    "    <p class=\"brand\">The Monoid LSTM Project</p>\n" +
    "    <p class=\"mast-note\">Static documentation generated from the two canonical Agda monoliths.</p>\n" +
    "  </header>\n" +
    "  <article class=\"document\">\n" +
    "    <section class=\"intro\" id=\"overview\">\n" +
    "      <p class=\"eyebrow\">Formal specification / proof surface</p>\n" +
    "      <h1>" + escapeHtml(page.title) + "</h1>\n" +
    "      <p class=\"lede\">" + escapeHtml(page.overview) + "</p>\n" +
    "      <p class=\"site-stats\">" + catalog.entries.length +
      " declarations | " + catalog.sourceFiles.length + " canonical source files</p>\n" +
    "    </section>\n" +
    "    <section class=\"section\" id=\"sources\">\n" +
    "      <h2>The two canonical source files</h2>\n" +
    "      <p class=\"section-lede\">Only these two monoliths are included in this presentation.</p>\n" +
    sourceCards + "\n" +
    "    </section>\n" +
    "    <section class=\"section\" id=\"russ\">\n" +
    "      <h2>Russian constructivism (RUSS)</h2>\n" +
    "      <p class=\"russ-status\">" + escapeHtml(page.consistencyStatus) + "</p>\n" +
    "      <p>" + escapeHtml(page.russTrustBoundary) + "</p>\n" +
    "    </section>\n" +
    "    <section class=\"section\" id=\"declarations\">\n" +
    "      <h2>Complete declaration index</h2>\n" +
    "      <p class=\"section-lede\">A static source-linked index of declarations in both monoliths.</p>\n" +
    declarationIndex + "\n" +
    "    </section>\n" +
    "    <footer class=\"footer\">Declaration presence is not evidence of theorem correctness or global consistency.</footer>\n" +
    "  </article>\n" +
    "</main>";

  const withTitle = template.replace(
    /<title>.*?<\/title>/s,
    "<title>" + escapeHtml(page.title) + "</title>"
  );
  return withTitle.replace("<!-- GENERATED_CONTENT -->", body);
};
