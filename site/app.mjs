import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { pathToFileURL } from "node:url";

const [catalogPath, pageModelPath, templatePath, outputPath] = process.argv.slice(2);
if (![catalogPath, pageModelPath, templatePath, outputPath].every(Boolean)) {
  throw new Error("usage: node site/app.mjs CATALOG.mjs AGDA_PAGE_MODEL.mjs TEMPLATE.html OUTPUT.html");
}

const [catalogModule, agdaModule, template] = await Promise.all([
  import(pathToFileURL(path.resolve(catalogPath)).href),
  import(pathToFileURL(path.resolve(pageModelPath)).href),
  readFile(templatePath, "utf8")
]);
const catalog = catalogModule.MonolithContent;
const page = agdaModule.default;
if (!catalog || !Object.isFrozen(catalog) ||
    !Object.isFrozen(catalog.sourceFiles) || !Object.isFrozen(catalog.entries) ||
    !catalog.entries.every(Object.isFrozen)) {
  throw new Error("catalog must be deeply frozen build data");
}
if (!page || page.sitePageIsStatic !== true ||
    typeof page.sitePageTitle !== "string" ||
    typeof page.sitePageOverview !== "string") {
  throw new Error("Agda-generated static page model is missing or invalid");
}
if (catalog.sourceFiles.length !== 2 ||
    catalog.sourceFiles[0] !== "FullCoupled/CanonicalLearnerMonolith.agda" ||
    catalog.sourceFiles[1] !== "FullCoupled/TheoremsMonolith.agda") {
  throw new Error("Pages may index only the two canonical monoliths");
}

const escapeHtml = (value) => String(value).replace(/[&<>"']/g, (char) => ({
  "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
})[char]);
const sourceUrl = (entry) =>
  "https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/" +
  entry.source + "#L" + entry.line;
const labelFor = (source) => source === catalog.sourceFiles[0]
  ? page.sitePageLearnerLabel
  : page.sitePageTheoremLabel;

const sourceCards = catalog.sourceFiles.map((source) => {
  const label = labelFor(source);
  return `<article class="source-record">
    <h3>${escapeHtml(label)}</h3>
    <p><code>${escapeHtml(source)}</code></p>
    <p><a href="https://github.com/JohnChristianD/Deep-Watkins-Monoid-LSTM/blob/main/${escapeHtml(source)}">Read canonical source</a></p>
  </article>`;
}).join("\n");

const declarationIndex = catalog.entries.map((entry) => `<article class="entry">
  <h3>${escapeHtml(entry.name)}</h3>
  <p class="signature">${escapeHtml(entry.signature || "(signature continues in source)")}</p>
  <p class="entry-meta">${escapeHtml(entry.category)} · ${escapeHtml(entry.source)}:${entry.line}</p>
  <p><a href="${escapeHtml(sourceUrl(entry))}">Open declaration in source</a></p>
</article>`).join("\n");

const body = `<main class="shell">
  <header class="masthead">
    <p class="brand">The Monoid LSTM Project</p>
    <p class="mast-note">Static documentation generated from the two canonical Agda monoliths.</p>
  </header>
  <article class="document">
    <section class="intro" id="overview">
      <p class="eyebrow">Formal specification / proof surface</p>
      <h1>${escapeHtml(page.sitePageTitle)}</h1>
      <p class="lede">${escapeHtml(page.sitePageOverview)}</p>
      <p class="site-stats">${catalog.entries.length} declarations · ${catalog.sourceFiles.length} canonical source files</p>
    </section>
    <section class="section" id="sources">
      <h2>The two canonical source files</h2>
      <p class="section-lede">Only these two monoliths are included in this presentation.</p>
      ${sourceCards}
    </section>
    <section class="section" id="russ">
      <h2>Russian constructivism (RUSS)</h2>
      <p class="russ-status">${escapeHtml(page.sitePageConsistencyStatus)}</p>
      <p>${escapeHtml(page.sitePageRUSSTrustBoundary)}</p>
    </section>
    <section class="section" id="declarations">
      <h2>Complete declaration index</h2>
      <p class="section-lede">A complete static listing of source-linked declarations.</p>
      ${declarationIndex}
    </section>
    <footer class="footer">Declaration presence is not evidence of theorem correctness or global consistency.</footer>
  </article>
</main>`;

if (!template.includes("<!-- GENERATED_CONTENT -->")) {
  throw new Error("HTML template must contain the generated-content marker");
}
const html = template
  .replace("<title>The Monoid LSTM Project - Learner and Theorem Monoliths</title>",
    `<title>${escapeHtml(page.sitePageTitle)}</title>`)
  .replace("<!-- GENERATED_CONTENT -->", body);
await writeFile(outputPath, html.endsWith("\n") ? html : html + "\n", "utf8");
console.log(`static-pages=pass declarations=${catalog.entries.length} runtime-javascript=none`);
