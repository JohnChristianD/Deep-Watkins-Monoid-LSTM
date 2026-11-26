-- Typed public surface for Lua Lanes 3.17.2.
-- Keep result and handle records nested under Lanes so callers refer to the
-- same nominal types exported by this module.

local record Lanes
   record WorkerResult
      status: any
      seconds: number
   end

   record LaneHandle
      join: function(self: LaneHandle): WorkerResult | nil, string | nil
   end

   configure: function(): Lanes
   gen: function(
      libraries: string,
      worker: function(command: string): WorkerResult
   ): function(command: string): LaneHandle
end

return Lanes
