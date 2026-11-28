-- Minimal typed LuaJIT FFI surface used by the POSIX worker launcher.
local record FFI
   cdef: function(declarations: string)
   new: function(ctype: string): {integer: any}
   C: {
      posix_spawnp: function(
         pid: {integer: any},
         file: string,
         file_actions: any,
         attributes: any,
         argv: {integer: any},
         envp: any
      ): number,
      waitpid: function(pid: any, child_state: {integer: any}, options: number): number,
      environ: any
   }
end

return FFI
