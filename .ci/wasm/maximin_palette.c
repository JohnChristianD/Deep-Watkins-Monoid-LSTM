/*
 * WebAssembly implementation of the site's perceptual maximin palette.
 * This mirrors the prior Elm arithmetic and greedy farthest-point rule:
 * CAT02 LMS -> opponent coordinates -> squared Euclidean distance.
 * The role count is supplied at runtime; the palette candidate budget is
 * role_count squared rather than a fixed six-color output.
 *
 * cos is intentionally an imported math primitive supplied by the browser
 * host. The module has no WASI, filesystem, or other runtime dependencies.
 */
extern double cos(double);

#define MAX_CANDIDATES 4096
#define TAU 6.283185307179586
#define SQRT3 1.7320508075688772
#define SQRT2 1.4142135623730951
#define SQRT6 2.449489742783178
#define DEG120 2.0943951023931953

typedef struct {
  double r, g, b;
  double L, A, B;
} Colour;

static Colour palette[MAX_CANDIDATES];
static Colour candidates[MAX_CANDIDATES];
static int palette_count = 0;

static double clamp01(double value) {
  if (value < 0.0) return 0.0;
  if (value > 1.0) return 1.0;
  return value;
}

static Colour make_colour(int index) {
  double extra = (double)(index - 90);
  double hue;
  double light;
  double chroma = 0.34;
  if (index < 90) {
    hue = TAU * (double)(index % 18) / 18.0;
    light = 0.28 + 0.045 * (double)(index % 5);
  } else {
    hue = TAU * (double)(((int)extra) % 720) / 720.0;
    light = 0.18 + 0.0005 * (double)(((int)extra) % 100);
  }

  Colour result;
  result.r = clamp01(light + chroma * cos(hue));
  result.g = clamp01(light + chroma * cos(hue - DEG120));
  result.b = clamp01(light + chroma * cos(hue + DEG120));

  /* CAT02 LMS matrix and the same opponent-coordinate transform as Elm. */
  double l = 0.7328 * result.r + 0.4296 * result.g - 0.1624 * result.b;
  double m = -0.7036 * result.r + 1.6975 * result.g + 0.0061 * result.b;
  double s = 0.0030 * result.r + 0.0136 * result.g + 0.9834 * result.b;
  result.L = (l + m + s) / SQRT3;
  result.A = (l - m) / SQRT2;
  result.B = (l + m - 2.0 * s) / SQRT6;
  return result;
}

static double distance_squared(Colour left, Colour right) {
  double dL = left.L - right.L;
  double dA = left.A - right.A;
  double dB = left.B - right.B;
  return dL * dL + dA * dA + dB * dB;
}

static double minimum_distance(int chosen_count, Colour candidate) {
  if (chosen_count <= 0) return 1.0 / 0.0;
  double best = distance_squared(palette[0], candidate);
  for (int i = 1; i < chosen_count; ++i) {
    double distance = distance_squared(palette[i], candidate);
    if (distance < best) best = distance;
  }
  return best;
}

/* Called with the semantic role count, so newly added roles expand the set. */
void palette_init(int role_count) {
  if (role_count < 1) role_count = 1;
  int candidate_count;
  if (role_count > MAX_CANDIDATES / role_count) {
    candidate_count = MAX_CANDIDATES;
  } else {
    candidate_count = role_count * role_count;
  }
  if (candidate_count > MAX_CANDIDATES) candidate_count = MAX_CANDIDATES;

  for (int i = 0; i < candidate_count; ++i) {
    candidates[i] = make_colour(i);
  }

  int remaining = candidate_count;
  palette_count = 0;
  while (remaining > 0 && palette_count < candidate_count) {
    Colour next = candidates[0];

    if (palette_count > 0) {
      double best = minimum_distance(palette_count, next);
      for (int i = 1; i < remaining; ++i) {
        double distance = minimum_distance(palette_count, candidates[i]);
        /* Strict greater-than preserves the incoming-first tie policy. */
        if (distance > best) {
          best = distance;
          next = candidates[i];
        }
      }
    }

    palette[palette_count++] = next;

    int retained = 0;
    for (int i = 0; i < remaining; ++i) {
      if (distance_squared(candidates[i], next) > 0.0) {
        candidates[retained++] = candidates[i];
      }
    }
    remaining = retained;
  }
}

int palette_size(void) {
  return palette_count;
}

/* Packed RRGGBB output; CSS formatting stays in the browser loader. */
int palette_color(int index) {
  if (index < 0 || index >= palette_count) return -1;
  Colour colour = palette[index];
  int r = (int)(255.0 * clamp01(colour.r) + 0.5);
  int g = (int)(255.0 * clamp01(colour.g) + 0.5);
  int b = (int)(255.0 * clamp01(colour.b) + 0.5);
  return (r << 16) | (g << 8) | b;
}
