-- Typed public surface for Lua Lanes 3.17.2.
-- configure() returns the configured module table. gen() returns a callable
-- lane factory; each launched lane returns a worker result through join().

local record WorkerResult
   status: any
   seconds: number
end

local record LaneHandle
   join: function(self: LaneHandle): WorkerResult | nil, string | nil
end

local record Lanes
   configure: function(): Lanes
   gen: function(
      libraries: string,
      worker: function(command: string): WorkerResult
   ): function(command: string): LaneHandle
end

return Lanes
