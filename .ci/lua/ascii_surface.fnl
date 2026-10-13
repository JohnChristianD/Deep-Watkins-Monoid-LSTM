(local fun (require :fun))
(local read-lines
  (fn [command]
  (local pipe (assert (io.popen command "r")))
  (local lines [])
  (each [line (pipe:lines)] (table.insert lines line))
  (pipe:close)
  lines))
(local read-file
  (fn [path] [path]
  (local file (assert (io.open path "rb")))
  (local content (file:read "*a"))
  (file:close)
  content))
(local files
  (fun.totable
    (fun.filter
      (fn [path] (not (= path "")))
      (read-lines "git ls-files '*.elm' '*.html' '*.js' | LC_ALL=C sort"))))
(each [_ path (ipairs files)]
  (local data (read-file path))
  (each [_ char (ipairs (fun.totable (string.gmatch data ".")))]
    (local byte (string.byte char))
    (when
      (or (> byte 127)
          (= byte 127)
          (and (< byte 32) (not (or (= byte 9) (= byte 10) (= byte 13)))))
      (io.stderr:write (.. "non-ASCII presentation surface: " path "\n"))
      (os.exit 1))))
(print (.. "ASCII presentation surface synchronized: " (# files) " tracked presentation files"))
