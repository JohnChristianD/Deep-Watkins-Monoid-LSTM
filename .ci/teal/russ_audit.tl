local source_files: {string} = {
   "FullCoupled/CanonicalLearnerMonolith.agda",
   "FullCoupled/TheoremsMonolith.agda"
}

local function read_file(path: string): string
   local file = assert(io.open(path, "r"), "cannot read " .. path)
   local content = assert(file:read("*a"), "cannot read contents of " .. path)
   file:close()
   return content
end

local function trim(value: string): string
   return string.gsub(string.gsub(value, "^%s+", ""), "%s+$", "")
end

local function count_postulate_blocks(source: string): number
   local count = 0
   for line in string.gmatch(source .. "\n", "(.-)\n") do
      local cleaned = trim(line)
      if cleaned == "postulate" or string.match(cleaned, "^postulate%s+") ~= nil then
         count = count + 1
      end
   end
   return count
end

local function has_token(source: string, token: string): boolean
   return string.find(source, token, 1, true) ~= nil
end

local function as_dhall_bool(value: boolean): string
   return value and "True" or "False"
end

local learner = read_file(source_files[1])
local theorem = read_file(source_files[2])
local learner_postulates = count_postulate_blocks(learner)
local theorem_postulates = count_postulate_blocks(theorem)
local output_path = arg[1] or "build/russ-audit.dhall"

local template = [[
{ canonicalModuleCount = %d
, learnerPostulateBlocks = %d
, theoremPostulateBlocks = %d
, learnerRUSSAssumptionsPresent = %s
, parametricEnumerabilityPresent = %s
, richmanCountableChoicePresent = %s
, conditionalExcludedMiddleProfilePresent = %s
, boundedMarkovSearchPresent = %s
, registerMachineEvaluatorPresent = %s
, intuitionisticObjectCalculusSoundnessPresent = %s
, objectCalculusRelativeConsistencyPresent = %s
, constructiveRiceTheoremPresent = %s
, concreteRiceProgrammingSystemPresent = False
, independentCombinedBasisModelProvided = False
, transitiveImportClosureCertified = False
, fullRUSSConsistencyCertified = False
}
]]

local content = string.format(
   template,
   #source_files,
   learner_postulates,
   theorem_postulates,
   as_dhall_bool(has_token(learner, "russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis")),
   as_dhall_bool(has_token(learner, "russParametricEnumerability")),
   as_dhall_bool(has_token(learner, "russCountableChoice")),
   as_dhall_bool(has_token(theorem, "excludedMiddleTheorem")),
   as_dhall_bool(has_token(theorem, "russSearchBounded")),
   as_dhall_bool(has_token(learner, "runMachineWithFuel")),
   as_dhall_bool(has_token(theorem, "russSoundness")),
   as_dhall_bool(has_token(theorem, "russCurrentBasisRelativeConsistency")),
   as_dhall_bool(has_token(theorem, "RiceTheorem"))
)

local output = assert(io.open(output_path, "w"), "cannot write " .. output_path)
output:write(content)
output:close()
print("russ-audit=generated; lexical inventory is not a proof certificate")
