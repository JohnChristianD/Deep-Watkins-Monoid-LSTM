-- Minimal LuaJIT FFI surface used by the POSIX worker launcher.
local record FFI
   cdef: function(declarations: string)
   new: function(ctype: string): any
   C: any
end

return FFI
