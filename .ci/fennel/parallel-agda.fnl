(local lanes (require :lanes))
(local fun (require :fun))

(local shell-quote (fn [value]
  (.. "'" (string.gsub value "'" "'\\''") "'")))

(local succeeded? (fn [status]
  (or (= status 0) (= status true))))

(local run! (fn [label command]
  (local status (os.execute command))
  (when (not (succeeded? status))
    (io.stderr:write
      (.. "parallel-agda=fail: " label " (status " (tostring status) ")\n"))
    (os.exit 1))))

(local agda-command (or (os.getenv "AGDA_COMMAND") "agda2hs-agda"))
(local temp-pipe (assert (io.popen "mktemp -d") "mktemp is required"))
(local temp-root (string.gsub (temp-pipe:read "*l") "\n$" ""))
(temp-pipe:close)
(assert (not (= temp-root "")) "mktemp did not return a directory")

(local learner-root (.. temp-root "/learner"))
(local theorem-root (.. temp-root "/theorem"))
(run! "create isolated workspaces"
  (.. "mkdir -p " (shell-quote (.. learner-root "/FullCoupled"))
      " " (shell-quote theorem-root)
      " && cp .agda-lib " (shell-quote learner-root)
      " && cp FullCoupled/CanonicalLearnerMonolith.agda "
      (shell-quote (.. learner-root "/FullCoupled/CanonicalLearnerMonolith.agda"))
      " && cp .agda-lib " (shell-quote theorem-root)
      " && cp FullCoupled/TheoremsMonolith.agda "
      (shell-quote (.. theorem-root "/TheoremsMonolith.agda"))))

(local entries
  [{:name "canonical learner"
    :root learner-root
    :module "FullCoupled/CanonicalLearnerMonolith.agda"
    :log (.. temp-root "/learner.log")}
   {:name "theorem monolith"
    :root theorem-root
    :module "TheoremsMonolith.agda"
    :log (.. temp-root "/theorem.log")}])

(local commands
  (fun.map
    (fn [entry]
      {:name entry.name
       :log entry.log
       :command
         (.. "cd " (shell-quote entry.root)
             " && " (shell-quote agda-command)
             " --local-interfaces --trace-imports=0 -i . "
             (shell-quote entry.module)
             " > " (shell-quote entry.log) " 2>&1")})
    (ipairs entries)))

(local launch (lanes.gen "*" (fn [command] (os.execute command))))
(local tasks [])
(local jobs [])
(each [entry commands]
  (table.insert jobs entry)
  (table.insert tasks (launch entry.command)))

(local statuses [])
(each [task tasks]
  (table.insert statuses (task:join)))

(local failed false)
(each [index entry (ipairs jobs)]
  (local status (. statuses index))
  (os.execute (.. "cat " (shell-quote entry.log)))
  (when (not (succeeded? status))
    (set failed true)
    (io.stderr:write
      (.. "parallel-agda=failed: " entry.name
          " (status " (tostring status) ")\n"))))

(os.execute (.. "rm -rf " (shell-quote temp-root)))
(when failed (os.exit 1))
(print "parallel-agda=pass; workers=2; isolated-local-interfaces=true")
