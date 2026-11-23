-- Parallel Agda checks using Lua Fun iterators and Lua Lanes.
-- Pure transformations build job descriptions; shell/process effects stay at the boundary.

local fun = require("fun")
local lanes = require("lanes").configure()

local function shell_quote(value)
  return "'" .. string.gsub(value, "'", "'\\''") .. "'"
end

local function succeeded(status)
  return status == 0 or status == true
end

local function run_checked(label, command)
  local status = os.execute(command)
  if not succeeded(status) then
    io.stderr:write(
      "parallel-agda=fail: " .. label .. " (status " .. tostring(status) .. ")\n"
    )
    os.exit(1)
  end
end

local function make_temp_root()
  local pipe = assert(io.popen("mktemp -d", "r"), "mktemp is required")
  local root = pipe:read("*l")
  pipe:close()
  assert(root and root ~= "", "mktemp did not return a directory")
  return root
end

local function make_entry(root, name, module, source_path)
  local work_root = root .. "/" .. name
  local module_path = work_root .. "/" .. module
  local log_path = root .. "/" .. name .. ".log"

  return {
    name = name,
    root = work_root,
    module = module,
    module_path = module_path,
    source_path = source_path,
    log = log_path
  }
end

local function command_for(entry, agda_command)
  return "cd " .. shell_quote(entry.root)
    .. " && " .. shell_quote(agda_command)
    .. " --local-interfaces --trace-imports=0 -i . "
    .. shell_quote(entry.module)
    .. " > " .. shell_quote(entry.log) .. " 2>&1"
end

local function main()
  local temp_root = make_temp_root()
  local agda_command = os.getenv("AGDA_COMMAND") or "agda2hs-agda"

  local entries = {
    {
      name = "learner",
      module = "FullCoupled/CanonicalLearnerMonolith.agda",
      source = "FullCoupled/CanonicalLearnerMonolith.agda"
    },
    {
      name = "theorem",
      module = "TheoremsMonolith.agda",
      source = "FullCoupled/TheoremsMonolith.agda"
    }
  }

  local jobs = fun.totable(fun.map(function(entry)
    local job = make_entry(temp_root, entry.name, entry.module, entry.source)
    job.command = command_for(job, agda_command)
    return job
  end, entries))

  run_checked(
    "create isolated workspaces",
    "mkdir -p " .. shell_quote(jobs[1].root) .. "/FullCoupled "
      .. shell_quote(jobs[2].root)
      .. " && cp .agda-lib " .. shell_quote(jobs[1].root)
      .. " && cp " .. shell_quote(jobs[1].source_path)
      .. " " .. shell_quote(jobs[1].module_path)
      .. " && cp .agda-lib " .. shell_quote(jobs[2].root)
      .. " && cp " .. shell_quote(jobs[2].source_path)
      .. " " .. shell_quote(jobs[2].module_path)
  )

  local launch = lanes.gen("*", function(command)
    return os.execute(command) or -1
  end)

  local tasks = fun.totable(fun.map(function(job)
    return launch(job.command)
  end, jobs))

  local outcomes = fun.totable(fun.map(function(index)
    local job = jobs[index]
    local status = tasks[index]:join()
    os.execute("cat " .. shell_quote(job.log))
    return {
      name = job.name,
      status = status,
      failed = not succeeded(status)
    }
  end, fun.range(1, #jobs)))

  os.execute("rm -rf " .. shell_quote(temp_root))

  local failed = fun.any(function(outcome)
    if outcome.failed then
      io.stderr:write(
        "parallel-agda=failed: " .. outcome.name
          .. " (status " .. tostring(outcome.status) .. ")\n"
      )
    end
    return outcome.failed
  end, outcomes)

  if failed then
    os.exit(1)
  end

  print("parallel-agda=pass; workers=2; isolated-local-interfaces=true")
end

main()
