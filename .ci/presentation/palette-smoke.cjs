const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");

const scriptPath = process.env.PALETTE_SCRIPT;
assert.ok(scriptPath, "PALETTE_SCRIPT must point at the built palette runtime");

const assigned = new Map();
const appNode = { id: "app" };
let elmInitialized = false;
const expectedRoles = [
  "--palette-ink", "--palette-paper", "--palette-accent",
  "--palette-accent-two", "--palette-quiet", "--palette-ink-on-accent"
];
const context = {
  document: {
    documentElement: { style: { setProperty: (name, value) => assigned.set(name, value) } },
    getElementById: id => id === "app" ? appNode : null
  },
  Elm: { Main: { init: options => {
    assert.equal(options.node, appNode);
    elmInitialized = true;
  } } },
  Math, Array, Number, String, console
};
vm.runInNewContext(fs.readFileSync(scriptPath, "utf8"), context, { filename: scriptPath });

assert.equal(elmInitialized, true, "Elm application must still initialize");
assert.deepEqual(Array.from(assigned.keys()).sort(), expectedRoles.slice().sort());
for (const value of assigned.values()) assert.match(value, /^rgb\(\d+ \d+ \d+\)$/);
assert.equal(new Set(assigned.values()).size, expectedRoles.length, "role colors must be distinct");
console.log("site-palette=pass (CAT02LMS, maximin, role-count adaptive)");
