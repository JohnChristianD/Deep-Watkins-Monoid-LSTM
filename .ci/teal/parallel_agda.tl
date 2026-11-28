local lanes_lib = require("lanes")
local lanes = lanes_lib.configure()

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

-- posix_spawnp is safe for concurrent worker threads; os.execute forks from
-- each Lua Lanes worker and can crash the LuaJIT coordinator.
local function run_process(command: string): number
   local ffi: any = require("ffi")
   ffi.cdef[[
      typedef int pid_t;
      typedef struct posix_spawn_file_actions_t posix_spawn_file_actions_t;
      typedef struct posix_spawnattr_t posix_spawnattr_t;
      int posix_spawnp(
         pid_t *pid,
         const char *file,
         const posix_spawn_file_actions_t *file_actions,
         const posix_spawnattr_t *attrp,
         char *const argv[],
         char *const envp[]
      );
      pid_t waitpid(pid_t pid, int *status, int options);
      extern char **environ;
   ]]
   local pid: any = ffi.new("pid_t[1]")
   local argv: any = ffi.new("char *[4]")
   argv[0] = "/bin/sh"
   argv[1] = "-c"
   argv[2] = command
   argv[3] = nil
   local spawn_status: number = ffi.C.posix_spawnp(pid, "/bin/sh", nil, nil, argv, ffi.C.environ)
   if spawn_status ~= 0 then
      return spawn_status
   end
   local child_status: any = ffi.new("int[1]")
   local waited: number = ffi.C.waitpid(pid[0], child_status, 0)
   if waited < 0 then
      return -1
   end
   return tonumber(child_status[0])
end

local function run_checked(label: string, command: string)
   local status: any = os.execute(command)
   if not succeeded(status) then
      io.stderr:write("parallel-agda=fail: " .. label .. " (status " .. tostring(status) .. ")\n")
      os.exit(1)
   end
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
-- data serially before launching workers, avoiding concurrent first-use copies.
run_checked("initialize shared Agda caches", shell_quote(agda_command) .. " --setup")

local launch: function(command: string): lanes_lib.LaneHandle = lanes.gen("*", function(command: string): lanes_lib.WorkerResult
   local started = os.time()
   local status = run_process(command)
   return {
      status = status,
      seconds = os.difftime(os.time(), started)
   }
end)

-- Exercise both successful and failing child exits through the same lane path
-- used by Agda workers. waitpid returns zero for exit 0 and a nonzero wait
-- status for exit 7.
local success_smoke, success_error = launch("exit 0"):join()
local failure_smoke, failure_error = launch("exit 7"):join()
if success_smoke is nil or failure_smoke is nil then
   io.stderr:write(
      "parallel-agda=fail: posix spawn lane error; success="
         .. tostring(success_error) .. "; failure=" .. tostring(failure_error) .. "\\n"
   )
   os.exit(1)
end
if not succeeded(success_smoke.status) or succeeded(failure_smoke.status) then
   io.stderr:write(
      "parallel-agda=fail: posix spawn status; success="
         .. tostring(success_smoke.status) .. "; failure=" .. tostring(failure_smoke.status) .. "\\n"
   )
   os.exit(1)
end
print("parallel-agda-spawn-smoke=pass")

local tasks: {lanes_lib.LaneHandle} = {}
for _, job in ipairs(jobs) do
   table.insert(tasks, launch(job.command))
end

local failed = false
for index, task in ipairs(tasks) do
   local job = jobs[index]
   local outcome, lane_error = task:join()
   if outcome is nil then
      io.stderr:write(
         "parallel-agda=failed: " .. job.name .. " (lane error "
            .. tostring(lane_error) .. ")\n"
      )
      failed = true
   else
      local status: any = outcome.status
      print("parallel-agda-worker=" .. job.name .. " seconds=" .. tostring(outcome.seconds))
      os.execute("cat " .. shell_quote(job.log))
      if not succeeded(status) then
         io.stderr:write("parallel-agda=failed: " .. job.name .. " (status " .. tostring(status) .. ")\n")
         failed = true
      end
   end
end

if failed then
   os.exit(1)
end
print("parallel-agda=pass; workers=" .. #jobs .. "; isolated-worker-interface-cache=true")
