local fun: any = require("fun")

local record Colour
   r: number
   g: number
   b: number
   L: number
   A: number
   B: number
end

local record SearchState
   distance: number
   colour: Colour | nil
end

local function read_file(path: string): string
   local file = assert(io.open(path, "r"), "cannot read " .. path)
   local content = assert(file:read("*a"), "cannot read contents of " .. path)
   file:close()
   return content
end

-- Generate the CAT02 LMS maximin palette at build time.
local stylesheet = read_file("site/site.less")
local role_source = assert(
   string.match(stylesheet, "%-%-palette%-role%-names:%s*([^;]+);"),
   "site/site.less must declare the semantic palette role registry"
)
local roles: {string} = {}
for role in string.gmatch(role_source, "%-%-[%w%-]+") do
   table.insert(roles, role)
end
assert(#roles > 0, "palette role registry is empty")

local max_candidates = 4096
local tau = 6.283185307179586
local sqrt3 = 1.7320508075688772
local sqrt2 = 1.4142135623730951
local sqrt6 = 2.449489742783178
local deg120 = 2.0943951023931953

local function clamp01(x: number): number
   return math.max(0.0, math.min(1.0, x))
end

local function make_colour(index: number): Colour
   local extra = index - 90
   local hue = index < 90
      and tau * (index % 18) / 18.0
      or tau * (extra % 720) / 720.0
   local light = index < 90
      and 0.28 + 0.045 * (index % 5)
      or 0.18 + 0.0005 * (extra % 100)
   local red = clamp01(light + 0.34 * math.cos(hue))
   local green = clamp01(light + 0.34 * math.cos(hue - deg120))
   local blue = clamp01(light + 0.34 * math.cos(hue + deg120))
   local l = (0.7328 * red + 0.4296 * green - 0.1624 * blue)
   local m = (-0.7036 * red + 1.6975 * green + 0.0061 * blue)
   local s = (0.0030 * red + 0.0136 * green + 0.9834 * blue)
   return {
      r = red,
      g = green,
      b = blue,
      L = (l + m + s) / sqrt3,
      A = (l - m) / sqrt2,
      B = (l + m - 2.0 * s) / sqrt6
   }
end

local function distance_squared(left: Colour, right: Colour): number
   local dL = left.L - right.L
   local dA = left.A - right.A
   local dB = left.B - right.B
   return dL * dL + dA * dA + dB * dB
end

local function minimum_distance(chosen: {Colour}, candidate: Colour): number
   if #chosen == 0 then
      return math.huge
   end
   local result: number = fun.foldl(
      function(best: number, colour: Colour): number
         return math.min(best, distance_squared(colour, candidate))
      end,
      math.huge,
      chosen
   )
   return result
end

local role_count = #roles
local candidate_count = math.min(max_candidates, role_count * role_count)
local candidates: {Colour} = fun.totable(
   fun.map(make_colour, fun.range(0, candidate_count - 1))
)
local chosen: {Colour} = {}

while #candidates > 0 and #chosen < role_count do
   local best: SearchState = fun.foldl(
      function(state: SearchState, candidate: Colour): SearchState
         local distance = minimum_distance(chosen, candidate)
         if distance > state.distance then
            return { distance = distance, colour = candidate }
         end
         return state
      end,
      { distance = -1, colour = nil },
      candidates
   )
   local next_colour: Colour = assert(best.colour)
   table.insert(chosen, next_colour)
   candidates = fun.totable(
      fun.filter(
         function(candidate: Colour): boolean
            return distance_squared(candidate, next_colour) > 0.0
         end,
         candidates
      )
   )
end

assert(#chosen == role_count, "palette generated " .. #chosen .. " roles, expected " .. role_count)

local function rgb_hex(colour: Colour): string
   return string.format(
      "#%02X%02X%02X",
      math.floor(255.0 * clamp01(colour.r) + 0.5),
      math.floor(255.0 * clamp01(colour.g) + 0.5),
      math.floor(255.0 * clamp01(colour.b) + 0.5)
   )
end

local arguments = {...}
local output_path = assert(arguments[1], "usage: palette_css.tl OUTPUT.css")
local output = assert(io.open(output_path, "w"), "cannot write " .. output_path)
output:write(":root {\n")
for index, role in ipairs(roles) do
   output:write(string.format("  %s: %s;\n", role, rgb_hex(chosen[index])))
end
output:write("}\n")
output:close()
print("cat02lms-palette-css=pass roles=" .. role_count)
