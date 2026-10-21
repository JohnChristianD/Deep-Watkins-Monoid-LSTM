const assert = require("node:assert/strict");
const fs = require("node:fs");

async function main() {
  const wasmFile = process.env.WASM_FILE;
  assert.ok(wasmFile, "WASM_FILE must point at the compiled palette module");

  const bytes = fs.readFileSync(wasmFile);
  const { instance } = await WebAssembly.instantiate(bytes, {
    env: { cos: Math.cos }
  });
  const palette = instance.exports;

  assert.equal(typeof palette.palette_init, "function");
  assert.equal(typeof palette.palette_size, "function");
  assert.equal(typeof palette.palette_color, "function");

  palette.palette_init(6);
  assert.equal(palette.palette_size(), 36, "six semantic roles should produce 36 candidates");
  const expectedFirstSix = [
    0x9e1c1c,
    0x4acc4a,
    0x1044a4,
    0x7e7e00,
    0x8424b8,
    0x088a8a
  ];
  for (let index = 0; index < expectedFirstSix.length; index += 1) {
    assert.equal(
      palette.palette_color(index) >>> 0,
      expectedFirstSix[index],
      "Wasm must preserve the existing CAT02LMS/maximin seed colors at index " + index
    );
  }

  palette.palette_init(7);
  assert.equal(palette.palette_size(), 49, "seven semantic roles should expand the candidate set");
  assert.notEqual(palette.palette_color(6), -1, "palette output must extend past the original six roles");
  console.log("wasm-maximin-regression=pass");
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
