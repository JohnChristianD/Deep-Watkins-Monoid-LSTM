"use strict";
const assert = require("node:assert/strict");
const path = require("node:path");
global.window = {};
const generated = process.argv[2];
assert.ok(generated, "usage: node .ci/presentation-smoke.cjs GENERATED_CONTENT.js");
require(path.resolve(generated));
require(path.resolve(__dirname, "../site/app.js"));
const catalog = global.window.MonolithContent;
const api = global.window.MonolithPage;
assert.ok(catalog && Array.isArray(catalog.entries), "generated catalog must load");
assert.ok(api && typeof api.filterEntries === "function", "native search API must load");
assert.deepEqual(catalog.sourceFiles, [
  "FullCoupled/CanonicalLearnerMonolith.agda",
  "FullCoupled/TheoremsMonolith.agda"
]);
assert.ok(catalog.entries.length > 0);
assert.ok(catalog.entries.every((e) => catalog.sourceFiles.includes(e.source)),
  "only canonical monolith sources may be indexed");
const all = api.filterEntries("", "all", catalog.entries);
const learner = api.filterEntries("", "learner", catalog.entries);
const theorem = api.filterEntries("", "theorem", catalog.entries);
assert.equal(all.length, catalog.entries.length);
assert.equal(learner.length + theorem.length, all.length);
assert.ok(learner.every((e) => e.source === catalog.sourceFiles[0]));
assert.ok(theorem.every((e) => e.source === catalog.sourceFiles[1]));
const sample = catalog.entries.find((e) => e.name && e.signature);
assert.ok(sample);
assert.ok(api.filterEntries("  " + sample.name.toUpperCase() + "  ", "all", catalog.entries)
  .some((e) => e.id === sample.id), "query must trim and ignore case");
const meta = [{id:"x",name:"Visible",signature:"Nat",source:"only-path",line:1,category:"only-category"}];
assert.equal(api.filterEntries("only-path", "all", meta).length, 0,
  "source path is display metadata, not searchable");
assert.equal(api.filterEntries("only-category", "all", meta).length, 0,
  "category is display metadata, not searchable");
console.log("native-pages-search-filter=pass declarations=" + all.length);