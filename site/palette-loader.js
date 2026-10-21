/*
 * Compute the CAT02LMS maximin semantic CSS palette in WebAssembly.
 * Native JavaScript owns content/search; Less owns layout. Palette failure
 * must not suppress or erase the declaration page.
 */
(async function () {
  const roleVariables = [
    "--palette-ink", "--palette-paper", "--palette-accent",
    "--palette-accent-two", "--palette-quiet", "--palette-ink-on-accent"
  ];
  try {
    const response = await fetch("site-palette.wasm");
    if (!response.ok) throw new Error("palette wasm fetch failed: " + response.status);
    const bytes = await response.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes, { env: { cos: Math.cos } });
    const palette = instance.exports;
    palette.palette_init(roleVariables.length);
    const toCss = (packed) => {
      const rgb = packed >>> 0;
      return "rgb(" + ((rgb >>> 16) & 255) + " " +
        ((rgb >>> 8) & 255) + " " + (rgb & 255) + ")";
    };
    for (let i = 0; i < roleVariables.length; ++i) {
      document.documentElement.style.setProperty(roleVariables[i], toCss(palette.palette_color(i)));
    }
  } catch (error) {
    console.error("CAT02LMS palette unavailable; CSS fallback colors remain active.", error);
  }
})();
