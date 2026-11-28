local record Entry
   name: string
   module: string
   source_path: string
end

local record Job
   name: string
   root: string
   module: string
   module_path: string
   module_dir: string
   source_path: string
   log: string
   command: string
end

local function shell_quote(value: string): string
   local quote = string.char(39)
   local escaped_quote = quote .. string.char(92) .. quote .. quote
   return quote .. string.gsub(value, quote, escaped_quote) .. quote
end

local function succeeded(status: any): boolean
   return status == 0 or status == true
end

-- Run subprocesses on the coordinator thread.  LuaJIT's os.execute
-- forks safely here; worker-thread fork/FFI interactions are avoided.
local function run_process(command: string): number
   local status: any = os.execute(command)
   if succeeded(status) then
      return 0
   end
   return 1
end

local function make_entry(root: string, entry: Entry, agda_command: string, profile_flag: string): Job
   local work_root = root .. "/" .. entry.name
   local parent = string.match(entry.module, "(.+)/[^/]+$")
   local module_dir = parent ~= nil and (work_root .. "/" .. parent) or work_root
   local module_path = work_root .. "/" .. entry.module
   local log_path = work_root .. "/" .. entry.name .. ".log"
   local command = "cd " .. shell_quote(work_root)
      .. " && " .. shell_quote(agda_command) .. profile_flag
      .. " --trace-imports=0 -i . "
      .. shell_quote(entry.module)
      .. " > " .. shell_quote(entry.name .. ".log") .. " 2>&1"
   return {
      name = entry.name,
      root = work_root,
      module = entry.module,
      module_path = module_path,
      module_dir = module_dir,
      source_path = entry.source_path,
      log = log_path,
      command = command
   }
end

local function copy_if_changed(source: string, destination: string): string
   return "if ! cmp -s " .. shell_quote(source) .. " " .. shell_quote(destination)
      .. "; then cp " .. shell_quote(source) .. " " .. shell_quote(destination) .. "; fi"
end

local cache_root = os.getenv("AGDA_WORKER_CACHE") or ".cache/agda-workers"
local agda_command = os.getenv("AGDA_COMMAND") or "agda2hs-agda"
local profile = os.getenv("AGDA_PROFILE")
local profile_flag = ""
if profile ~= nil and profile ~= "" then
   profile_flag = " --profile=" .. shell_quote(profile) .. " +RTS -s -RTS"
end

local entries: {Entry} = {
   {
      name = "learner",
      module = "FullCoupled/CanonicalLearnerMonolith.agda",
      source_path = "FullCoupled/CanonicalLearnerMonolith.agda"
   },
   {
      name = "theorem",
      module = "TheoremsMonolith.agda",
      source_path = "FullCoupled/TheoremsMonolith.agda"
   }
}

local jobs: {Job} = {}
for _, entry in ipairs(entries) do
   table.insert(jobs, make_entry(cache_root, entry, agda_command, profile_flag))
end

local setup_commands: {string} = {}
for _, job in ipairs(jobs) do
   table.insert(
      setup_commands,
      "mkdir -p " .. shell_quote(job.module_dir)
         .. " && rm -rf " .. shell_quote(job.root .. "/Haskell")
         .. " && cp -R Haskell " .. shell_quote(job.root)
         .. " && " .. copy_if_changed(".agda-lib", job.root .. "/.agda-lib")
         .. " && " .. copy_if_changed(job.source_path, job.module_path)
   )
end

run_checked(
   "prepare persistent isolated workspaces",
   "mkdir -p " .. shell_quote(cache_root) .. " && " .. table.concat(setup_commands, " && ")
)

-- Both lanes share XDG_CACHE_HOME. Initialize the base library and primitive
-- data serially before running isolated checks, avoiding concurrent first-use copies.
run_checked("initialize shared Agda caches", shell_quote(agda_command) .. " --setup")

-- Execute isolated Agda workspaces serially.  This keeps the worker
-- interface cache isolated while avoiding unsafe fork calls from Lua lanes.
local failed = false
for _, job in ipairs(jobs) do
   local started = os.time()
   local status = run_process(job.command)
   print("parallel-agda-worker=" .. job.name .. " seconds=" .. tostring(os.difftime(os.time(), started)))
   os.execute("cat " .. shell_quote(job.log))
   if status ~= 0 then
      io.stderr:write("parallel-agda=failed: " .. job.name .. " (status " .. tostring(status) .. ")\\n")
      failed = true
   end
end

if failed then
   os.exit(1)
end
print("parallel-agda=pass; workers=" .. #jobs .. "; isolated-worker-interface-cache=true")
