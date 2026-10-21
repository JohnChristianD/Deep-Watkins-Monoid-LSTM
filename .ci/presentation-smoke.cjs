"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { pathToFileURL } = require("node:url");

async function main() {
  const generated = process.argv[2];
  const runtime = process.argv[3];
  assert.ok(generated && runtime,
    "usage: node .ci/presentation-smoke.cjs GENERATED_CONTENT.js AGDA_JS_RUNTIME_DIR");
  global.window = {};
  require(path.resolve(generated));
  const catalog = global.window.MonolithContent;
  assert.ok(catalog && Array.isArray(catalog.entries), "generated catalog must load");
  assert.deepEqual(catalog.sourceFiles, [
    "FullCoupled/CanonicalLearnerMonolith.agda",
    "FullCoupled/TheoremsMonolith.agda"
  ]);
  assert.ok(catalog.entries.length > 0);
  assert.ok(catalog.entries.every((e) => catalog.sourceFiles.includes(e.source)),
    "only canonical monolith sources may be indexed");

  fs.copyFileSync(path.resolve(__dirname, "../site/app.mjs"),
    path.join(path.resolve(runtime), "app.mjs"));
  await import(pathToFileURL(path.join(path.resolve(runtime), "app.mjs")).href);
  const api = global.window.MonolithPage;
  assert.ok(api && typeof api.filteredEntries === "function",
    "DOM adapter must expose Agda-backed pure filtering API");

  const all = api.filteredEntries("", "all", catalog.entries);
  const learner = api.filteredEntries("", "learner", catalog.entries);
  const theorem = api.filteredEntries("", "theorem", catalog.entries);
  assert.equal(all.length, catalog.entries.length);
  assert.equal(learner.length + theorem.length, all.length);
  assert.ok(learner.every((e) => e.source === catalog.sourceFiles[0]));
  assert.ok(theorem.every((e) => e.source === catalog.sourceFiles[1]));
  const sample = catalog.entries.find((e) => e.name && e.signature);
  assert.ok(sample);
  assert.ok(api.filteredEntries("  " + sample.name.toUpperCase() + "  ", "all", catalog.entries)
    .some((e) => e.id === sample.id), "Agda semantics must trim and ignore ASCII case");
  const meta = [{id:"x",name:"Visible",signature:"Nat",source:"only-path",line:1,category:"only-category"}];
  assert.equal(api.filteredEntries("only-path", "all", meta).length, 0,
    "source path is display metadata, not searchable");
  assert.equal(api.filteredEntries("only-category", "all", meta).length, 0,
    "category is display metadata, not searchable");
  console.log("agda-js-pages-search-filter=pass declarations=" + all.length);
}
main().catch((error) => { console.error(error); process.exitCode = 1; });
