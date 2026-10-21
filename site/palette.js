/* Pure JavaScript CAT02LMS maximin palette runtime.
 * The entries are CSS semantic roles, not a fixed palette size. The candidate
 * set scales as roles² and the selected palette scales as roles. For the
 * current six roles this preserves the prior Elm candidate ordering/transform.
 */
(function () {
  "use strict";
  const roleVariables = [
    "--palette-ink", "--palette-paper", "--palette-accent",
    "--palette-accent-two", "--palette-quiet", "--palette-ink-on-accent"
  ];
  const TAU = 6.283185307179586;
  const SQRT3 = 1.7320508075688772;
  const SQRT2 = 1.4142135623730951;
  const SQRT6 = 2.449489742783178;
  const DEG120 = 2.0943951023931953;

  function clamp01(value) { return Math.max(0, Math.min(1, value)); }

  /* CAT02 LMS matrix: preserve the existing three-channel transform. */
  function cat02Lms(rgb) {
    return [
      0.7328 * rgb.r + 0.4296 * rgb.g - 0.1624 * rgb.b,
      -0.7036 * rgb.r + 1.6975 * rgb.g + 0.0061 * rgb.b,
      0.0030 * rgb.r + 0.0136 * rgb.g + 0.9834 * rgb.b
    ];
  }

  function toOpponent(rgb) {
    const [l, m, s] = cat02Lms(rgb);
    return {
      rgb,
      l: (l + m + s) / SQRT3,
      a: (l - m) / SQRT2,
      b: (l + m - 2 * s) / SQRT6
    };
  }

  function distanceSquared(left, right) {
    const dl = left.l - right.l;
    const da = left.a - right.a;
    const db = left.b - right.b;
    return dl * dl + da * da + db * db;
  }

  function candidateRgb(index, roleCount) {
    const candidateCount = roleCount * roleCount;
    let hueCount = 18;
    let lightCount = 5;
    let hueIndex = index % 18;
    let lightIndex = index % 5;
    let light;

    /* Preserve the original grid until it would repeat after 90 candidates. */
    if (candidateCount > 90) {
      hueCount = Math.ceil(Math.sqrt(candidateCount));
      lightCount = Math.ceil(candidateCount / hueCount);
      hueIndex = index % hueCount;
      lightIndex = Math.floor(index / hueCount);
      light = lightCount <= 1
        ? 0.28
        : 0.18 + 0.45 * (lightIndex / (lightCount - 1));
    } else {
      light = 0.28 + 0.045 * lightIndex;
    }

    const hue = TAU * hueIndex / hueCount;
    const chroma = 0.34;
    return {
      r: clamp01(light + chroma * Math.cos(hue)),
      g: clamp01(light + chroma * Math.cos(hue - DEG120)),
      b: clamp01(light + chroma * Math.cos(hue + DEG120))
    };
  }

  function minimumDistance(chosen, candidate) {
    return chosen.reduce(
      (best, item) => Math.min(best, distanceSquared(item, candidate)),
      Infinity
    );
  }

  function maximinPalette(roleCount) {
    if (roleCount <= 0) return [];
    let candidates = Array.from(
      { length: roleCount * roleCount },
      (_, index) => toOpponent(candidateRgb(index, roleCount))
    );
    let chosen = [];

    while (chosen.length < roleCount && candidates.length > 0) {
      let next = candidates[0];
      if (chosen.length > 0) {
        let best = minimumDistance(chosen, next);
        for (let index = 1; index < candidates.length; index += 1) {
          const distance = minimumDistance(chosen, candidates[index]);
          if (distance > best) {
            best = distance;
            next = candidates[index];
          }
        }
      }
      chosen = chosen.concat([next]);
      candidates = candidates.filter(
        candidate => distanceSquared(candidate, next) > 0
      );
    }
    return chosen;
  }

  function rgbCss(rgb) {
    return "rgb("
      + Math.round(255 * clamp01(rgb.r)) + " "
      + Math.round(255 * clamp01(rgb.g)) + " "
      + Math.round(255 * clamp01(rgb.b)) + ")";
  }

  const palette = maximinPalette(roleVariables.length);
  if (palette.length !== roleVariables.length) {
    throw new Error("maximin palette did not produce every semantic role");
  }
  roleVariables.forEach(function (name, index) {
    document.documentElement.style.setProperty(name, rgbCss(palette[index].rgb));
  });
  /* Elm remains the interactive application; Less owns presentation. */
  Elm.Main.init({ node: document.getElementById("app") });
})();
