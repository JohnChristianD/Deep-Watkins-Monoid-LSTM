import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { PageModel } from "./page-model.mjs";
import { renderStaticPage } from "./render.mjs";

const [catalogPath, templatePath, outputPath] = process.argv.slice(2);
if (![catalogPath, templatePath, outputPath].every(Boolean)) {
  throw new Error("usage: node site/app.mjs CATALOG.mjs TEMPLATE.html OUTPUT.html");
}

const [catalogModule, template] = await Promise.all([
  import(pathToFileURL(path.resolve(catalogPath)).href),
  readFile(templatePath, "utf8")
]);
const html = renderStaticPage(catalogModule.MonolithContent, PageModel, template);
await writeFile(outputPath, html.endsWith("\n") ? html : html + "\n", "utf8");
console.log("static-pages=pass declarations=" +
  catalogModule.MonolithContent.entries.length + " browser-javascript=none");
