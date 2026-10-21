(local read-file
  (fn [path]
    (local file (assert (io.open path "r") (.. "cannot read " path)))
    (local content (file:read "*a"))
    (file:close)
    content))

; Generate the CAT02 LMS maximin palette at build time. The browser receives
; only ordinary CSS custom properties: no WebAssembly, math host, or palette
; mutation at runtime.
(local stylesheet (read-file "site/site.less"))
(local role-source
  (assert
    (string.match stylesheet "%-%-palette%-role%-names:%s*([^;]+);")
    "site/site.less must declare the semantic palette role registry"))
(local roles [])
(each [role (string.gmatch role-source "%-%-[%w%-]+")]
  (table.insert roles role))
(assert (> (# roles) 0) "palette role registry is empty")

(local MAX-CANDIDATES 4096)
(local TAU 6.283185307179586)
(local SQRT3 1.7320508075688772)
(local SQRT2 1.4142135623730951)
(local SQRT6 2.449489742783178)
(local DEG120 2.0943951023931953)

(local clamp01 (fn [x]
  (math.max 0.0 (math.min 1.0 x))))

(local make-colour (fn [index]
  (local extra (- index 90))
  (local hue (if (< index 90)
      (/ (* TAU (% index 18)) 18.0)
      (/ (* TAU (% extra 720)) 720.0)))
  (local light (if (< index 90)
      (+ 0.28 (* 0.045 (% index 5)))
      (+ 0.18 (* 0.0005 (% extra 100)))))
  (local r (clamp01 (+ light (* 0.34 (math.cos hue)))))
  (local g (clamp01 (+ light (* 0.34 (math.cos (- hue DEG120))))))
  (local b (clamp01 (+ light (* 0.34 (math.cos (+ hue DEG120))))))
  (local l (+ (* 0.7328 r) (* 0.4296 g) (* -0.1624 b)))
  (local m (+ (* -0.7036 r) (* 1.6975 g) (* 0.0061 b)))
  (local s (+ (* 0.0030 r) (* 0.0136 g) (* 0.9834 b)))
  {:r r :g g :b b
   :L (/ (+ l m s) SQRT3)
   :A (/ (- l m) SQRT2)
   :B (/ (+ l m (* -2.0 s)) SQRT6)}))

(local distance-squared (fn [left right]
  (local dL (- left.L right.L))
  (local dA (- left.A right.A))
  (local dB (- left.B right.B))
  (+ (* dL dL) (* dA dA) (* dB dB))))

(local minimum-distance (fn [chosen candidate]
  (if (= (# chosen) 0)
      math.huge
      (do
        (local best math.huge)
        (each [_ colour (ipairs chosen)]
          (set best (math.min best (distance-squared colour candidate))))
        best))))

(local role-count (# roles))
(local candidate-count (math.min MAX-CANDIDATES (* role-count role-count)))
(local candidates [])
(for [index 0 (- candidate-count 1)]
  (table.insert candidates (make-colour index)))

(local chosen [])
(while (and (> (# candidates) 0) (< (# chosen) role-count))
  (local next-colour (. candidates 1))
  (when (> (# chosen) 0)
    (local best (minimum-distance chosen next-colour))
    ; Strict greater-than preserves candidate-order ties, matching the
    ; existing C11 implementation.
    (for [index 2 (# candidates)]
      (local candidate (. candidates index))
      (local distance (minimum-distance chosen candidate))
      (when (> distance best)
        (set best distance)
        (set next-colour candidate))))
  (table.insert chosen next-colour)
  (local remaining [])
  (each [_ candidate (ipairs candidates)]
    (when (> (distance-squared candidate next-colour) 0.0)
      (table.insert remaining candidate)))
  (set candidates remaining))

(assert (= (# chosen) role-count)
  (.. "palette generated " (# chosen) " roles, expected " role-count))

(local rgb-hex (fn [colour]
  (string.format "#%02X%02X%02X"
    (math.floor (+ (* 255.0 (clamp01 colour.r)) 0.5))
    (math.floor (+ (* 255.0 (clamp01 colour.g)) 0.5))
    (math.floor (+ (* 255.0 (clamp01 colour.b)) 0.5)))))

(local output-path (assert (. arg 1) "usage: palette_css.fnl OUTPUT.css"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))
(output:write ":root {\n")
(each [index role (ipairs roles)]
  (output:write (string.format "  %s: %s;\n" role (rgb-hex (. chosen index)))))
(output:write "}\n")
(output:close)
(print (.. "cat02lms-palette-css=pass roles=" role-count))
