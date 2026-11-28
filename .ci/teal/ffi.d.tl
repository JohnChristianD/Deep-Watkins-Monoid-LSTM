-- Typed subset of LuaJIT FFI used by the POSIX worker launcher.
local record FFI_C
   posix_spawnp: function(pid: {any}, file: string, file_actions: any, attrp: any, argv: {any}, envp: any): number
   waitpid: function(pid: any, status: {any}, options: number): number
   environ: any
end

local record FFI
   cdef: function(declarations: string)
   new: function(ctype: string): {any}
   C: FFI_C
end

return FFI
