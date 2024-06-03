import Time.Time
import Time.IO

namespace Time

/-! This module contains definitions related to time, such as structures for representing system time,
intervals, and durations. -/

/-- `Instant` represents a place in time with second and nanoseconds precision. Does not represent
norminal data as months and days. -/
structure Instant where
  secs: Nat
  nanos: Nat
  deriving Repr

/-- `Duration` represents a time span with second and nanoseconds precision. Does not represent
norminal data as months and days. -/
structure Duration where
  secs: Int
  nanos: Int
  deriving Repr

/-- Subtract two instants and returns the duration between two instants.-/
def Instant.sub (t₁ t₂ : Instant) : Duration :=
  let nsPerSecond := 1000000000
  let nsec_diff := (t₁.nanos : Int) - (t₂.nanos : Int)
  let sec_diff := (t₁.secs : Int) - (t₂.secs : Int)
  if sec_diff > 0 && nsec_diff < 0 then
    { secs := (sec_diff - 1), nanos := (nsec_diff + nsPerSecond) }
  else if sec_diff < 0 && nsec_diff > 0 then
    { secs := (sec_diff + 1), nanos := (nsec_diff - nsPerSecond) }
  else
    { secs := sec_diff, nanos := nsec_diff }

instance : HSub Instant Instant Duration where
  hSub := Instant.sub

/-- Gets the current instant in time -/
def Instant.now : IO Instant := do
  let (secs, nanos) ← Time.primGetCurrentEpochTime
  pure (Instant.mk secs nanos)

/-- Returns a `Duration` that represents the time span betwen an `instant` and now -/
def Instant.elapsed (instant: Instant) : IO Duration := do
  let now ← Instant.now
  return now - instant

/-- Returns a `Duration` that represents the time span betwen an `start`, another instant. -/
def Instant.since (instant: Instant) (since: Instant) : Duration :=
  Instant.sub since instant

/-- Returns a `Duration` representing the given number of second. -/
def Duration.ofSecs (second: Second) : Duration :=
  { secs := second.val, nanos := 0 }

/-- Returns a `Duration` representing the given number of minute. -/
def Duration.ofMinutes (minute: Minute) : Duration :=
  { secs := minute * 60, nanos := 0 }

/-- Returns a `Duration` representing the given number of hour. -/
def Duration.ofHours (hour: Hour) : Duration :=
  { secs := hour * 3600, nanos := 0 }

/-- Constructs a `Duration` from the given `Time`. -/
def Duration.ofTime (time: Time) : Duration :=
  { secs := TimeLike.hour time * 3600 + TimeLike.minute time * 60 + TimeLike.second time
  , nanos := 0 }
