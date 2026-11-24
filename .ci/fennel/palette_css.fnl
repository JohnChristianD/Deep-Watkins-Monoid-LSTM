(local fun (require :fun))

(local read-file
  (fn [path]
    (let [file (assert (io.open path "r") (.. "cannot read " path))
          content (:read file "*a")]
      (:close file)
      content)))

; Generate the CAT02 LMS maximin palette at build time.
(local stylesheet (read-file "site/site.less"))
(local role-source
  (assert
    (string.match stylesheet "%-%-palette%-role%-names:%s*([^;]+);")
    "site/site.less must declare the semantic palette role registry"))
(local roles [])
(each [role (string.gmatch role-source "%-%-[%w%-]+")]
  (table.insert roles role))
(assert (> (# roles) 0) "palette role registry is empty")

(local max-candidates 4096)
(local tau 6.283185307179586)
(local sqrt3 1.7320508075688772)
(local sqrt2 1.4142135623730951)
(local sqrt6 2.449489742783178)
(local deg120 2.0943951023931953)

(local clamp01
  (fn [x] (math.max 0.0 (math.min 1.0 x))))

(local make-colour
  (fn [index]
    (let* [extra (- index 90)
           hue (if (< index 90)
                   (/ (* tau (% index 18)) 18.0)
                   (/ (* tau (% extra 720)) 720.0))
           light (if (< index 90)
                     (+ 0.28 (* 0.045 (% index 5)))
                     (+ 0.18 (* 0.0005 (% extra 100))))
           red (clamp01 (+ light (* 0.34 (math.cos hue))))
           green (clamp01 (+ light (* 0.34 (math.cos (- hue deg120)))))
           blue (clamp01 (+ light (* 0.34 (math.cos (+ hue deg120)))))
           l (+ (* 0.7328 red) (* 0.4296 green) (* -0.1624 blue))
           m (+ (* -0.7036 red) (* 1.6975 green) (* 0.0061 blue))
           ss (+ (* 0.0030 red) (* 0.0136 green) (* 0.9834 blue))]
      {:r red :g green :b blue
       :L (/ (+ l m ss) sqrt3)
       :A (/ (- l m) sqrt2)
       :B (/ (+ l m (* -2.0 ss)) sqrt6)})))

(local distance-squared
  (fn [left right]
    (let [dL (- (. left :L) (. right :L))
          dA (- (. left :A) (. right :A))
          dB (- (. left :B) (. right :B))]
      (+ (* dL dL) (* dA dA) (* dB dB)))))

(local minimum-distance
  (fn [chosen candidate]
    (if (= (# chosen) 0)
        math.huge
        (fun.foldl
          (fn [best colour]
            (math.min best (distance-squared colour candidate)))
          math.huge
          chosen))))

(local role-count (# roles))
(local candidate-count (math.min max-candidates (* role-count role-count)))
(local candidates
  (fun.totable (fun.map make-colour (fun.range 0 (- candidate-count 1)))))
(local chosen [])

(while (and (> (# candidates) 0) (< (# chosen) role-count))
  (let [best
        (fun.foldl
          (fn [state candidate]
            (let [distance (minimum-distance chosen candidate)]
              (if (> distance (. state :distance))
                  {:distance distance :colour candidate}
                  state)))
          {:distance -1 :colour nil}
          candidates)
        next-colour (. best :colour)]
    (table.insert chosen next-colour)
    (set candidates
      (fun.totable
        (fun.filter
          (fn [candidate]
            (> (distance-squared candidate next-colour) 0.0))
          candidates)))))

(assert (= (# chosen) role-count)
  (.. "palette generated " (# chosen) " roles, expected " role-count))

(local rgb-hex
  (fn [colour]
    (string.format "#%02X%02X%02X"
      (math.floor (+ (* 255.0 (clamp01 (. colour :r))) 0.5))
      (math.floor (+ (* 255.0 (clamp01 (. colour :g))) 0.5))
      (math.floor (+ (* 255.0 (clamp01 (. colour :b))) 0.5)))))

(local output-path (assert (. arg 1) "usage: palette_css.fnl OUTPUT.css"))
(local output (assert (io.open output-path "w") (.. "cannot write " output-path)))
(output:write ":root {\\n")
(each [index role (ipairs roles)]
  (output:write (string.format "  %s: %s;\\n" role (rgb-hex (. chosen index)))))
(output:write "}\\n")
(output:close)
(print (.. "cat02lms-palette-css=pass roles=" role-count))
