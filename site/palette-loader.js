/* Small browser host for the palette WebAssembly module. */
(async function () {
  const appNode = document.getElementById("app");
  const roleVariables = [
    "--palette-ink",
    "--palette-paper",
    "--palette-accent",
    "--palette-accent-two",
    "--palette-quiet",
    "--palette-ink-on-accent"
  ];

  try {
    const response = await fetch("site-palette.wasm");
    if (!response.ok) throw new Error("palette wasm fetch failed: " + response.status);
    const bytes = await response.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes, {
      env: { cos: Math.cos }
    });
    const palette = instance.exports;
    palette.palette_init(roleVariables.length);

    const toCss = (packed) => {
      const rgb = packed >>> 0;
      const r = (rgb >>> 16) & 255;
      const g = (rgb >>> 8) & 255;
      const b = rgb & 255;
      return "rgb(" + r + " " + g + " " + b + ")";
    };

    for (let i = 0; i < roleVariables.length; ++i) {
      document.documentElement.style.setProperty(roleVariables[i], toCss(palette.palette_color(i)));
    }

    /* Elm retains document/search interaction; Less owns layout, Wasm owns palette math. */
    Elm.Main.init({ node: appNode });

    const swatches = document.getElementById("wasm-palette");
    if (!swatches) throw new Error("palette container was not rendered");
    const count = palette.palette_size();
    for (let i = 0; i < count; ++i) {
      const swatch = document.createElement("div");
      swatch.className = "swatch";
      swatch.title = "maximin-" + (i + 1);
      swatch.style.background = toCss(palette.palette_color(i));
      swatches.appendChild(swatch);
    }

    const caption = document.getElementById("wasm-palette-caption");
    if (caption) {
      caption.textContent = "CAT02LMS / " + count +
        " maximin colors. Selection runs in the local WebAssembly module.";
    }
  } catch (error) {
    if (appNode) {
      appNode.textContent = "The local maximin palette could not initialize. " +
        "The presentation was stopped rather than showing a mismatched palette.";
    }
    console.error(error);
  }
})();
