(local fun (require :fun))
(local lanes-lib (require :lanes))
(local lanes (lanes-lib.configure))

(local shell-quote
  (fn [value]
    (.. "'" (string.gsub (tostring value) "'" "'\\''") "'")))

(local succeeded?
  (fn [status] (or (= status 0) (= status true))))

(local run-checked
  (fn [label command]
    (let [status (os.execute command)]
      (when (not (succeeded? status))
        (io.stderr:write
          (.. "parallel-agda=fail: " label " (status " (tostring status) ")\\n"))
        (os.exit 1)))))

(local make-entry
  (fn [root name module source-path]
    (let* [work-root (.. root "/" name)
           parent (string.match module "(.+)/[^/]+$")
           module-dir (if parent (.. work-root "/" parent) work-root)]
      {:name name
       :root work-root
       :module module
       :module-path (.. work-root "/" module)
       :module-dir module-dir
       :source-path source-path
       :log (.. root "/" name ".log")})))

(local copy-if-changed
  (fn [source destination]
    (.. "if ! cmp -s " (shell-quote source) " " (shell-quote destination)
        "; then cp " (shell-quote source) " " (shell-quote destination) "; fi")))

(local command-for
  (fn [entry agda-command profile-flag]
    (.. "cd " (shell-quote (. entry :root))
        " && " (shell-quote agda-command) profile-flag
        " --local-interfaces --trace-imports=0 -i . "
        (shell-quote (. entry :module))
        " > " (shell-quote (. entry :log)) " 2>&1")))

(local cache-root (or (os.getenv "AGDA_WORKER_CACHE") ".cache/agda-workers"))
(local agda-command (or (os.getenv "AGDA_COMMAND") "agda2hs-agda"))
(local profile (os.getenv "AGDA_PROFILE"))
(local profile-flag
  (if (and profile (not (= profile "")))
      (.. " --profile=" (shell-quote profile) " +RTS -s -RTS")
      ""))

(local entries
  [{:name "learner"
    :module "FullCoupled/CanonicalLearnerMonolith.agda"
    :source-path "FullCoupled/CanonicalLearnerMonolith.agda"}
   {:name "theorem"
    :module "TheoremsMonolith.agda"
    :source-path "FullCoupled/TheoremsMonolith.agda"}])

(local jobs
  (fun.totable
    (fun.map
      (fn [entry]
        (let [job (make-entry cache-root (. entry :name)
                              (. entry :module) (. entry :source-path))]
          (assoc job :command (command-for job agda-command profile-flag)))
      entries)))

(local setup-commands
  (fun.totable
    (fun.map
      (fn [job]
        (.. "mkdir -p " (shell-quote (. job :module-dir))
            " && " (copy-if-changed ".agda-lib" (.. (. job :root) "/.agda-lib"))
            " && " (copy-if-changed (. job :source-path) (. job :module-path)))
      jobs)))

(run-checked
  "prepare persistent isolated workspaces"
  (.. "mkdir -p " (shell-quote cache-root) " && "
      (table.concat setup-commands " && ")))

(local launch
  ((. lanes :gen) "*" (fn [command] (or (os.execute command) -1))))

(local tasks
  (fun.totable
    (fun.map (fn [job] (launch (. job :command))) jobs)))

(local outcomes
  (fun.totable
    (fun.map
      (fn [index]
        (let* [job (. jobs index)
               task (. tasks index)
               status ((. task :join) task)]
          (os.execute (.. "cat " (shell-quote (. job :log))))
          {:name (. job :name)
           :status status
           :failed (not (succeeded? status))}))
      (fun.range 1 (# jobs)))))

(local failed
  (fun.any
    (fn [outcome]
      (when (. outcome :failed)
        (io.stderr:write
          (.. "parallel-agda=failed: " (. outcome :name)
              " (status " (tostring (. outcome :status)) ")\\n")))
      (. outcome :failed))
    outcomes))

(when failed (os.exit 1))
(print (.. "parallel-agda=pass; workers=" (tostring (# jobs))
           "; persistent-local-interface-cache=true"))
