local function shell_quote(value: string): string
   local quote = string.char(39)
   local escaped_quote = quote .. string.char(92) .. quote .. quote
   return quote .. string.gsub(value, quote, escaped_quote) .. quote
end

local function succeeded(status: any): boolean
   return status == 0 or status == true
end

local function run_checked(label: string, command: string)
   local started = os.time()
   local status: any = os.execute(command)
   local elapsed = os.difftime(os.time(), started)
   print("ci-timing=" .. label .. " seconds=" .. tostring(elapsed))
   if not succeeded(status) then
      io.stderr:write("ci-lane=fail: " .. label .. " (status " .. tostring(status) .. ")\n")
      os.exit(1)
   end
end

local function read_file(path: string): string
   local file = assert(io.open(path, "r"), "cannot read " .. path)
   local content = assert(file:read("*a"), "cannot read contents of " .. path)
   file:close()
   return content
end

local function write_file(path: string, content: string)
   local file = assert(io.open(path, "w"), "cannot write " .. path)
   file:write(content)
   file:close()
end

local function check_teal_sources()
   local files: {string} = {
      ".ci/teal/ci.tl",
      ".ci/teal/pages.tl",
      ".ci/teal/palette_css.tl",
      ".ci/teal/parallel_agda.tl",
      ".ci/teal/russ_audit.tl"
   }
   run_checked(
      "require LuaFun and Lua Lanes Teal declarations",
      "test -s " .. shell_quote(".ci/teal/fun.d.tl")
         .. " && test -s " .. shell_quote(".ci/teal/lanes.d.tl")
   )
   for _, path in ipairs(files) do
      run_checked(
         "Teal typecheck " .. path,
         "tl check -I " .. shell_quote(".ci/teal") .. " " .. shell_quote(path)
      )
   end
end

local function compile_teal(path: string): string
   local name = assert(string.match(path, "([^/]+)%.tl$"), "expected a .tl source path")
   local directory = "build/teal"
   local copied_source = directory .. "/" .. name .. ".tl"
   local generated_lua = directory .. "/" .. name .. ".lua"

   run_checked("create Teal runtime directory", "mkdir -p " .. shell_quote(directory))
   run_checked(
      "stage Teal runtime source " .. path,
      "cp " .. shell_quote(path) .. " " .. shell_quote(copied_source)
   )
   run_checked(
      "generate isolated Lua runtime " .. path,
      "tl gen -I " .. shell_quote(".ci/teal") .. " --output "
         .. shell_quote(generated_lua) .. " " .. shell_quote(copied_source)
   )
   return generated_lua
end

local function check_build_source()
   run_checked(
      "reject legacy script sources",
      "if git ls-files -z -- '*.fnl' '*.yue' '*.lua' | grep -q .; then echo 'legacy/non-Teal script source remains in tracked files' >&2; exit 1; fi"
   )
   run_checked(
      "reject legacy toolchain references",
      "if grep -Eiq 'fennel|yuescript|\\.fnl|\\.yue' flake.nix .github/workflows/github-pages.yml; then echo 'legacy script toolchain reference remains' >&2; exit 1; fi"
   )
   run_checked(
      "reject Streamly dependencies and imports in tracked sources",
      "if git grep -Eni 'streamly|Streamly\\\\.' -- . ':!.ci/teal/ci.tl'; then echo 'Streamly source reference remains' >&2; exit 1; fi"
   )
   run_checked(
      "reject only LuaFun contraction iterators",
      "if grep -Eni '(^|[^[:alnum:]_])(duplicate|replicate|xrepeat|cycle)([^[:alnum:]_]|$)' .ci/teal/pages.tl .ci/teal/palette_css.tl .ci/teal/parallel_agda.tl .ci/teal/russ_audit.tl; then echo 'contraction iterator found' >&2; exit 1; fi"
   )
   print("build-source-audit=pass; Teal; contraction-only LuaFun exclusions")
end

local function check_agda_learner()
   local source = "FullCoupled/CanonicalLearnerMonolith.agda"
   run_checked(
      "require Agda 2.9 erased-quotients spelling",
      "grep -Fxq -- '--erased-quotients' " .. shell_quote(source)
         .. " && ! grep -Fxq -- '--erased-quotient' " .. shell_quote(source)
   )
   run_checked(
      "keep unsafe Agda options local to learner",
      "test ! -e .ci/agda/global-options.txt"
         .. " && grep -Fxq -- '--type-in-type' " .. shell_quote(source)
         .. " && grep -Fxq -- '--rewriting' " .. shell_quote(source)
         .. " && ! grep -Fq 'AGDA_NO_GLOBAL_OPTIONS' flake.nix"
         .. " && ! grep -Fq 'AGDA_NO_GLOBAL_OPTIONS' .ci/teal/parallel_agda.tl"
         .. " && grep -Fq 'agda2hsTool system}/bin/agda2hs' flake.nix"
   )
   local theorem_source = "FullCoupled/TheoremsMonolith.agda"
   run_checked(
      "require safe delayed coinduction",
      "grep -Fq -- '--safe' " .. shell_quote(theorem_source)
         .. " && ! grep -Fq -- '--guardedness' " .. shell_quote(theorem_source)
         .. " && ! grep -Fq -- '--type-in-type' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'open import Agda.Builtin.Coinduction public' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'data Conat : Set where' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'infinity = suc∞ (♯ infinity)' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'data ConatStream (A : Set) : Set where' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'consConatStream : A → ∞ (ConatStream A) → ConatStream A' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'data CodyadicDigitStream : Set where' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'codyadicDigitStep : SignedBinaryDigit → ∞ CodyadicDigitStream → CodyadicDigitStream' " .. shell_quote(theorem_source)
         .. " && ! grep -Fq '  coinductive' " .. shell_quote(theorem_source)
         .. " && grep -Fq 'suc∞ predecessor +∞ b = suc∞ (♯ (♭ predecessor +∞ b))' " .. shell_quote(theorem_source)
   )
   run_checked(
      "reject LSTM and epsilon-greedy paths",
      "if grep -Eiq 'lstm|epsilon[ _-]?greedy|e[_-]?z[_-]?greedy' " .. shell_quote(source) .. "; then echo 'forbidden recurrent/action selector found' >&2; exit 1; fi"
   )
   run_checked(
      "reject DeepSets and postponed FQF code",
      "if grep -Eiq 'DeepSets|FQF' " .. shell_quote(source) .. "; then echo 'postponed architecture found in learner source' >&2; exit 1; fi"
   )
   run_checked(
      "reject retired actor and max-gradient learner",
      "if grep -Eiq 'softsign|Softsign|policyProbabilities|sampleAction|ActionHead|streamMaxGrad|networkTrainStepSARSA([^0-9]|$)|maxGrad' " .. shell_quote(source) .. "; then echo 'retired actor-critic or max-gradient path remains' >&2; exit 1; fi"
   )
   run_checked(
      "reject floating-point runtime types",
      "if grep -Eiq '(^|[^[:alnum:]_])(Float|Float32|Float64)([^[:alnum:]_]|$)' " .. shell_quote(source) .. "; then echo 'floating-point runtime type found' >&2; exit 1; fi"
   )
   run_checked(
      "require Q8.24 IQN32 Double-SARSA learner symbols",
      "for symbol in 'qShift = 24' 'qOne     = 16777216' q4Tanh q4TanhGrad IDBDConfig IDBDParameter idbdStep l2GradientDecay NoisyDense32 DuelingIQN32 TwinDuelingCritics doubleSARSA0Target networkStart networkTrainStepSARSA0 iterativeCHAD qQuantileHuberPairGradient; do grep -Fq \"$symbol\" " .. shell_quote(source) .. " || exit 1; done"
   )
   run_checked(
      "require unchanged Agda import surface",
      "for import in 'open import Haskell.Prelude public' 'open import Haskell.Data.Int public' 'open import Haskell.Data.Bits public' 'open import Agda.Builtin.Equality.Rewrite public'; do grep -Fq \"$import\" FullCoupled/CanonicalLearnerMonolith.agda || exit 1; done"
   )
   run_checked(
      "require ReLU on recurrent candidate and output",
      "grep -Fq 'candidate = qRelu candidateInput' " .. shell_quote(source) .. " && grep -Fq 'hiddenAfter = qRelu mixPre' " .. shell_quote(source)
   )
   print("learner-source-audit=pass; Q8.24; IQN32; Double SARSA(0); IDBD; Quantmoid4")
end

local function check_agda_theorem()
   run_checked(
      "parallel Agda checks in a clean LuaJIT process",
      "luajit " .. shell_quote(compile_teal(".ci/teal/parallel_agda.tl"))
   )
   run_checked("create Agda2HS output directory", "mkdir -p build/agda2hs")
   run_checked(
      "Agda2HS extract canonical learner",
      "agda2hs " .. shell_quote("FullCoupled/CanonicalLearnerMonolith.agda") .. " -o " .. shell_quote("build/agda2hs")
   )
   run_checked(
      "verify extracted Haskell module",
      "test -s build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs"
   )
   run_checked("create GHC check output directory", "mkdir -p build/ghc")
   run_checked(
      "GHC typecheck extracted learner with phase and RTS timings",
      "ghc-check -ddump-timings -fno-code -fforce-recomp -i./build/agda2hs -odir build/ghc -hidir build/ghc build/agda2hs/FullCoupled/CanonicalLearnerMonolith.hs +RTS -s -RTS"
   )
   print("agda2hs-and-ghc-check=pass-relative-to-declared-imports-and-primitives")
end

local function check_russ_audit()
   run_checked("create RUSS audit directory", "mkdir -p build")
   run_checked(
      "generate RUSS trust inventory",
      "luajit " .. shell_quote(compile_teal(".ci/teal/russ_audit.tl")) .. " build/russ-audit.dhall"
   )
   run_checked("typecheck RUSS inventory", "dhall type --file build/russ-audit.dhall")
   print("russ-audit=generated; lexical inventory is not a proof certificate")
end

local function check_pages()
   local out = os.getenv("PAGES_OUTPUT_DIR") or "build/pages"
   local palette = out .. "/palette.css"
   local base_css = out .. "/base.css"
   local css = out .. "/site.css"
   local html = out .. "/index.html"

   run_checked("create static Pages output", "mkdir -p " .. shell_quote(out))
   run_checked("generate palette CSS", "luajit " .. shell_quote(compile_teal(".ci/teal/palette_css.tl")) .. " " .. shell_quote(palette))
   run_checked("compile Less stylesheet", "lessc site/site.less " .. shell_quote(base_css))
   write_file(css, read_file(palette) .. "\n" .. read_file(base_css))
   run_checked("render static HTML", "luajit " .. shell_quote(compile_teal(".ci/teal/pages.tl")) .. " " .. shell_quote(html))

   local generated_html = read_file(html)
   local generated_css = read_file(css)
   local published_readme = out .. "/README.md"
   write_file(published_readme, read_file("README.md"))
   assert(string.find(generated_html, 'href="site.css"', 1, true) ~= nil, "published HTML is missing its stylesheet link")
   assert(#read_file(published_readme) > 0, "published README copy is empty")
   assert(string.find(generated_html, 'href="README.md"', 1, true) ~= nil, "published landing page is missing its README link")
   assert(string.find(generated_html, 'class="hero"', 1, true) ~= nil, "published landing page is missing its hero")
   assert(string.find(generated_html, 'class="model-panel"', 1, true) ~= nil, "published landing page is missing its model specification")
   assert(string.find(generated_html, 'class="verification"', 1, true) ~= nil, "published landing page is missing its verification boundary")
   assert(string.find(generated_html, "<script", 1, true) == nil, "published HTML must remain static")
   assert(string.find(generated_css, ".shell", 1, true) ~= nil, "compiled LESS is missing the page shell")
   assert(string.find(generated_css, ".hero", 1, true) ~= nil, "compiled LESS is missing the hero layout")
   assert(string.find(generated_css, ".verification", 1, true) ~= nil, "compiled LESS is missing the verification section")
   assert(string.find(generated_css, "max-width: 800px", 1, true) ~= nil, "compiled LESS is missing its mobile layout")

   os.remove(palette)
   os.remove(base_css)
   print("static-pages=generated; less-css=validated; browser-JavaScript=none")
end

local arguments = {...}
local lane = arguments[1] or ""
if lane == "AgdaLearner" then
   check_build_source()
   check_teal_sources()
   check_agda_learner()
   check_agda_theorem()
elseif lane == "AgdaTheorem" then
   check_build_source()
   check_teal_sources()
   check_agda_theorem()
elseif lane == "RUSS" then
   check_build_source()
   check_teal_sources()
   check_russ_audit()
   check_agda_theorem()
elseif lane == "Pages" then
   check_build_source()
   check_teal_sources()
   check_pages()
elseif lane == "All" then
   check_build_source()
   check_teal_sources()
   check_agda_learner()
   check_russ_audit()
   check_pages()
   check_agda_theorem()
else
   io.stderr:write("usage: luajit build/teal/ci.lua AgdaLearner|AgdaTheorem|RUSS|Pages|All\\n")
   os.exit(2)
end
