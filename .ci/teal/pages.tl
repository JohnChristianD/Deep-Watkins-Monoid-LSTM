local function write_file(path: string, content: string)
   local file = assert(io.open(path, "w"), "cannot write " .. path)
   file:write(content)
   file:close()
end

local arguments = {...}
local output_path = assert(arguments[1], "usage: pages.tl OUTPUT.html")
local lines: {string} = {
   "<!doctype html>",
   '<html lang="en">',
   "<head>",
   '<meta charset="utf-8">',
   '<meta name="viewport" content="width=device-width,initial-scale=1">',
   '<meta name="description" content="Agda-first Q8.24 recurrent distributional learner.">',
   "<title>Deep Watkins RNN</title>",
   '<link rel="stylesheet" href="site.css">',
   "</head>",
   "<body>",
   '<main class="shell">',
   '<header class="masthead"><p class="eyebrow">Agda / Q8.24 / IQN32</p></header>',
   '<section class="intro">',
   "<h1>Deep Watkins RNN</h1>",
   "<p>The repository README is the sole project documentation. It describes the learner, update semantics, numeric model, and verification boundary.</p>",
   '<p><a class="readme-link" href="README.md">Read README.md</a></p>',
   "</section>",
   '<footer class="footer"><p>Source: <a href="FullCoupled/CanonicalLearnerMonolith.agda">Canonical Agda learner</a>.</p></footer>',
   "</main>",
   "</body>",
   "</html>"
}
local html = table.concat(lines, "\n")

assert(string.find(html, 'href="README.md"', 1, true) ~= nil, "README link is missing")
assert(string.find(html, "<script", 1, true) == nil, "static Pages output must not contain scripts")
write_file(output_path, html)
print("static-pages=README-only landing page")
