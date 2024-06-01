namespace Time

@[extern "get_current_epoch_seconds"]
protected opaque primGetCurrentEpochSeconds : IO Nat

@[extern "get_current_epoch_time"]
protected opaque primGetCurrentEpochTime : IO (Nat × Nat)

@[extern "time_offset"]
protected opaque primTimeOffset : IO Int
