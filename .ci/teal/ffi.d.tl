-- Minimal typed LuaJIT FFI surface used by the POSIX worker launcher.
local type CData = {any}

local record FFI_C
   posix_spawnp: function(
      pid: CData,
      file: string,
      file_actions: CData | nil,
      attrp: CData | nil,
      argv: CData,
      envp: CData
   ): number
   waitpid: function(pid: any, status: CData, options: number): number
   environ: CData
end

local record FFI
   cdef: function(declarations: string)
   new: function(ctype: string): CData
   C: FFI_C
end

return FFI
