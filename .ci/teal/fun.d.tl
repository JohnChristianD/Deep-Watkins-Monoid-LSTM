-- Typed LuaFun surface used by palette_css.tl.
-- LuaFun wraps iterators as callable tables and returns iterator triples.

local type Iterator<T> = record<T>
   gen: function(any, any): any, T
   param: any
   state: any
end

local record LuaFun
   foldl: function<A, T>(
      reducer: function(A, T): A,
      initial: A,
      values: {T}
   ): A

   map: function<A, B>(
      mapper: function(A): B,
      source: Iterator<A>,
      param?: any,
      state?: any
   ): Iterator<B>, any, any

   range: function(
      start: number,
      stop: number,
      step?: number
   ): Iterator<number>, any, any

   totable: function<T>(
      source: Iterator<T>,
      param?: any,
      state?: any
   ): {T}

   filter: function<T>(
      predicate: function(T): boolean,
      values: {T}
   ): Iterator<T>, any, any
end

return LuaFun
