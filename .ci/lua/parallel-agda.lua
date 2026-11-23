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

local function make_entry(root, name, module, source_path)
  local work_root = root .. "/" .. name
  local module_path = work_root .. "/" .. module
  local log_path = root .. "/" .. name .. ".log"
  local parent = module:match("(.+)/[^/]+$")
  local module_dir = parent and (work_root .. "/" .. parent) or work_root

  return {
    name = name,
    root = work_root,
    module = module,
    module_path = module_path,
    module_dir = module_dir,
    source_path = source_path,
    log = log_path
  }
end

local function copy_if_changed(source, destination)
  return "if ! cmp -s " .. shell_quote(source) .. " " .. shell_quote(destination)
    .. "; then cp " .. shell_quote(source) .. " " .. shell_quote(destination) .. "; fi"
end

local function command_for(entry, agda_command, profile_flag)
  return "cd " .. shell_quote(entry.root)
    .. " && " .. shell_quote(agda_command) .. profile_flag
    .. " --local-interfaces --trace-imports=0 -i . "
    .. shell_quote(entry.module)
    .. " > " .. shell_quote(entry.log) .. " 2>&1"
end

local function main()
  -- Keep independent local-interface caches under .cache so CI can restore them.
  -- Copy only changed source files: unchanged mtimes preserve Agda's cache hits.
  local cache_root = os.getenv("AGDA_WORKER_CACHE") or ".cache/agda-workers"
  local agda_command = os.getenv("AGDA_COMMAND") or "agda2hs-agda"
  local profile = os.getenv("AGDA_PROFILE")
  local profile_flag = profile and profile ~= ""
    and (" --profile=" .. shell_quote(profile) .. " +RTS -s -RTS")
    or ""

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
    local job = make_entry(cache_root, entry.name, entry.module, entry.source)
    job.command = command_for(job, agda_command, profile_flag)
    return job
  end, entries))

  local setup_commands = fun.totable(fun.map(function(job)
    return "mkdir -p " .. shell_quote(job.module_dir)
      .. " && " .. copy_if_changed(".agda-lib", job.root .. "/.agda-lib")
      .. " && " .. copy_if_changed(job.source_path, job.module_path)
  end, jobs))

  run_checked(
    "prepare persistent isolated workspaces",
    "mkdir -p " .. shell_quote(cache_root)
      .. " && " .. table.concat(setup_commands, " && ")
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

  local failed = fun.any(function(outcome)
    if outcome.failed then
      io.stderr:write(
        "parallel-agda=failed: " .. outcome.name
          .. " (status " .. tostring(outcome.status) .. ")\\n"
      )
    end
    return outcome.failed
  end, outcomes)

  if failed then
    os.exit(1)
  end

  print(
    "parallel-agda=pass; workers=" .. tostring(#jobs)
      .. "; persistent-local-interface-cache=true"
  )
end

main()
