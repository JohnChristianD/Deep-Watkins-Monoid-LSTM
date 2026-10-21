"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");

const outputPath = process.argv[2];
assert.ok(outputPath, "usage: node .ci/presentation-smoke.cjs GENERATED_INDEX.html");
const html = fs.readFileSync(outputPath, "utf8");

assert.ok(html.includes("<!doctype html>"), "static document must be HTML5");
assert.ok(html.includes("Canonical learner semantics"), "learner source section must exist");
assert.ok(html.includes("Theorem and proof monolith"), "theorem source section must exist");
assert.ok(html.includes("Global RUSS consistency: not certified"),
  "the page must not claim a consistency proof");
assert.ok(html.includes("Complete declaration index"), "static declaration index must exist");
assert.ok(html.includes("FullCoupled/CanonicalLearnerMonolith.agda"));
assert.ok(html.includes("FullCoupled/TheoremsMonolith.agda"));
assert.ok(!html.includes("<!-- GENERATED_CONTENT -->"), "template marker must be replaced");
assert.ok(!/<script\b/i.test(html), "published HTML must not ship JavaScript");
assert.ok(!/<input\b/i.test(html), "published HTML must not include search controls");
assert.ok(!/<button\b/i.test(html), "published HTML must not include filter or selection controls");
assert.ok(!/filter-row|entry-select|addEventListener|siteSearchMatches|filterEntries/i.test(html),
  "published HTML must contain no interactive search/filter semantics");

console.log("static-pages-smoke=pass runtime-javascript=none");
