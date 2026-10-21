"use strict";
const assert = require("node:assert/strict");
const path = require("node:path");
const { pathToFileURL } = require("node:url");

(async () => {
  global.window = {};
  const generatedCatalog = process.argv[2];
  const agdaJavaScript = process.argv[3];
  assert.ok(generatedCatalog && agdaJavaScript,
    "usage: node .ci/presentation-smoke.cjs GENERATED_CONTENT.js AGDA_JS_MODULE.mjs");

  require(path.resolve(generatedCatalog));
  const catalog = global.window.MonolithContent;
  assert.ok(catalog && Array.isArray(catalog.entries), "generated catalog must load");
  assert.deepEqual(catalog.sourceFiles, [
    "FullCoupled/CanonicalLearnerMonolith.agda",
    "FullCoupled/TheoremsMonolith.agda"
  ]);
  assert.ok(catalog.entries.length > 0);
  assert.ok(catalog.entries.every((entry) => catalog.sourceFiles.includes(entry.source)),
    "only the two canonical monolith sources may be indexed");

  const compiled = await import(pathToFileURL(path.resolve(agdaJavaScript)).href);
  const pageSearchMatches = compiled.default && compiled.default.siteSearchMatches;
  assert.equal(typeof pageSearchMatches, "function",
    "Agda --js output must export siteSearchMatches");

  // Apply the curried Agda function; this test intentionally contains no
  // JavaScript reimplementation of query normalization or membership rules.
  const matches = (query, scope, name, signature, source) =>
    pageSearchMatches(query)(scope)(name)(signature)(source);
  assert.equal(matches("  RUSS  ", "all", "RussianRecursiveMathematicsAssumptions", "Nat",
    catalog.sourceFiles[0]), true, "Agda search must trim query whitespace and ignore case");
  assert.equal(matches("", "learner", "Visible", "Nat", catalog.sourceFiles[1]), false,
    "learner scope must match exactly the learner monolith");
  assert.equal(matches("", "theorem", "Visible", "Nat", catalog.sourceFiles[0]), false,
    "theorem scope must match exactly the theorem monolith");
  assert.equal(matches("FullCoupled/CanonicalLearnerMonolith.agda", "all",
    "Visible", "Nat", catalog.sourceFiles[0]), false,
    "source path is display metadata, not a searchable field");

  const all = catalog.entries.filter((entry) =>
    matches("", "all", entry.name, entry.signature, entry.source));
  const learner = catalog.entries.filter((entry) =>
    matches("", "learner", entry.name, entry.signature, entry.source));
  const theorem = catalog.entries.filter((entry) =>
    matches("", "theorem", entry.name, entry.signature, entry.source));
  assert.equal(all.length, catalog.entries.length);
  assert.equal(learner.length + theorem.length, all.length);
  assert.ok(learner.every((entry) => entry.source === catalog.sourceFiles[0]));
  assert.ok(theorem.every((entry) => entry.source === catalog.sourceFiles[1]));

  console.log("agda-js-pages-search=pass declarations=" + all.length);
})().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
