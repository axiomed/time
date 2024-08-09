import Time

def main : IO Unit := do
  let r ← Std.Time.Instant.now
  IO.println s!"ata {repr r}"
  let r ← Std.Time.Timestamp.now
  IO.println s!"ata {repr r}"
  let r ← Std.Time.Instant.highResolutionNow
  IO.println s!"ata {repr r}"
