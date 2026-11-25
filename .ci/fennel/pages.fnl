(local write-file
  (fn [path content]
    (let [file (assert (io.open path "w") (.. "cannot write " path))]
      (:write file content)
      (:close file))))

(local output-path (assert (. arg 1) "usage: pages.fnl OUTPUT.html"))
(local html
  (table.concat
    ["<!doctype html>"
     "<html lang=\"en\">"
     "<head>"
     "<meta charset=\"utf-8\">"
     "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
     "<meta name=\"description\" content=\"Agda-first Q8.24 recurrent distributional learner.\">"
     "<title>Deep Watkins RNN</title>"
     "<link rel=\"stylesheet\" href=\"site.css\">"
     "</head>"
     "<body>"
     "<main class=\"shell\">"
     "<header class=\"masthead\"><p class=\"eyebrow\">Agda / Q8.24 / IQN32</p></header>"
     "<section class=\"intro\">"
     "<h1>Deep Watkins RNN</h1>"
     "<p>The repository README is the sole project documentation. It describes the learner, update semantics, numeric model, and verification boundary.</p>"
     "<p><a class=\"readme-link\" href=\"README.md\">Read README.md</a></p>"
     "</section>"
     "<footer class=\"footer\"><p>Source: <a href=\"FullCoupled/CanonicalLearnerMonolith.agda\">Canonical Agda learner</a>.</p></footer>"
     "</main>"
     "</body>"
     "</html>"]
    "\n"))

(assert (string.find html "href=\"README.md\"" 1 true)
  "README link is missing")
(assert (not (string.find html "<script" 1 true))
  "static Pages output must not contain scripts")
(write-file output-path html)
(print "static-pages=README-only landing page")
