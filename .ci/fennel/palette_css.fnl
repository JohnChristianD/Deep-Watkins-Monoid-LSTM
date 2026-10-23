(local fun (require :fun))

; Pure colour-space and maximin-selection core. Candidate/chosen collections
; are persistent linked lists. File access is isolated at this outer adapter.

(local read-file (fn [path]
  (local file (assert (io.open path "r") (.. "cannot read " path)))
  (local content (file:read "*a"))
  (file:close)
  content))

(local stylesheet (read-file "site/site.less"))
(local role-source
  (assert
    (string.match stylesheet "%-%-palette%-role%-names:%s*([^;]+);")
    "site/site.less must declare the semantic palette role registry"))
(local roles
  (fun.totable
    (fun.map (fn [role] role)
      (string.gmatch role-source "%-%-[%w%-]+"))))

(local MAX-CANDIDATES 4096)
(local TAU 6.283185307179586)
(local SQRT3 1.7320508075688772)
(local SQRT2 1.4142135623730951)
(local SQRT6 2.449489742783178)
(local DEG120 2.0943951023931953)

(local clamp01 (fn [x] (math.max 0.0 (math.min 1.0 x))))

(local make-colour (fn [index]
  (local extra (- index 90))
  (local hue
    (if (< index 90)
        (/ (* TAU (% index 18)) 18.0)
        (/ (* TAU (% extra 720)) 720.0)))
  (local light
    (if (< index 90)
        (+ 0.28 (* 0.045 (% index 5)))
        (+ 0.18 (* 0.0005 (% extra 100)))))
  (local r (clamp01 (+ light (* 0.34 (math.cos hue)))))
  (local g (clamp01 (+ light (* 0.34 (math.cos (- hue DEG120)))))
  (local b (clamp01 (+ light (* 0.34 (math.cos (+ hue DEG120)))))
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

(local make-candidates (fn make-candidates [index limit]
  (if (>= index limit)
      nil
      {:head (make-colour index)
       :tail (make-candidates (+ index 1) limit)})))

(local list-count (fn list-count [values]
  (if values (+ 1 (list-count values.tail)) 0)))

(local list-append (fn list-append [values value]
  (if values
      {:head values.head :tail (list-append values.tail value)}
      {:head value :tail nil})))

(local list-ref (fn list-ref [values index]
  (if (or (not values) (<= index 0))
      nil
      (if (= index 1) values.head (list-ref values.tail (- index 1)))))

(local minimum-distance (fn minimum-distance [chosen candidate]
  (if (not chosen)
      math.huge
      (math.min
        (distance-squared chosen.head candidate)
        (minimum-distance chosen.tail candidate))))

(local farthest (fn farthest [chosen candidates]
  (if (not candidates)
      nil
      (if (not candidates.tail)
          {:colour candidates.head
           :score (minimum-distance chosen candidates.head)}
          (do
            (local first-colour candidates.head)
            (local first-score (minimum-distance chosen first-colour))
            (local rest-best (farthest chosen candidates.tail))
            (if (>= first-score rest-best.score)
                {:colour first-colour :score first-score}
                rest-best)))))

(local without-colour (fn without-colour [candidates chosen]
  (if (not candidates)
      nil
      (do
        (local rest (without-colour candidates.tail chosen))
        (if (> (distance-squared candidates.head chosen) 0.0)
            {:head candidates.head :tail rest}
            rest))))

(local choose-colours (fn choose-colours [candidates chosen target]
  (if (>= (list-count chosen) target)
      chosen
      (if (not candidates)
          chosen
          (do
            (local selected
              (if chosen
                  (. (farthest chosen candidates) :colour)
                  candidates.head))
            (local remaining (without-colour candidates selected))
            (choose-colours remaining
              (list-append chosen selected) target)))))

(local rgb-hex (fn [colour]
  (string.format "#%02X%02X%02X"
    (math.floor (+ (* 255.0 (clamp01 colour.r)) 0.5))
    (math.floor (+ (* 255.0 (clamp01 colour.g)) 0.5))
    (math.floor (+ (* 255.0 (clamp01 colour.b)) 0.5))))

(local render-css (fn render-css [index colour-count colours]
  (if (> index colour-count)
      "}\n"
      (.. (string.format "  %s: %s;\n"
            (. roles index)
            (rgb-hex (list-ref colours index)))
          (render-css (+ index 1) colour-count colours))))

(local role-count (# roles))
(local candidate-count (math.min MAX-CANDIDATES (* role-count role-count)))
(local candidates (make-candidates 0 candidate-count))
(local chosen (choose-colours candidates nil role-count))
(assert (= (list-count chosen) role-count)
  (.. "palette generated " (list-count chosen) " roles, expected " role-count))

(local css (.. ":root {\n" (render-css 1 role-count chosen)))
(local output-path (assert (. arg 1) "usage: palette_css.fnl OUTPUT.css"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))
(output:write css)
(output:close)
(print (.. "cat02lms-palette-css=pass roles=" role-count))
