/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Bounded
import Time.Time

open Time

/--
`Instant` represents a place in time with second and nanoseconds precision.
-/
structure Instant where
  seconds : Second.Offset
  nanos : Nanosecond.Ordinal
  valid : seconds.val ≥ 0 ∧ nanos.val ≥ 0
  deriving Repr

/--
Time duration with nanosecond precision. This type allows negative duration.
-/
structure Duration where
  seconds : Second.Offset
  nanos : Nanosecond.Span

namespace Instant

/--
Gets the difference of two `Instant` in a `Duration`.
-/
def sub (t₁ t₂ : Instant) : Duration :=
  let nsec_diff := (t₁.nanos).subBounds (t₂.nanos)
  let sec_diff := (t₁.seconds) - (t₂.seconds)
  if h : sec_diff.val > 0 ∧ nsec_diff.val ≤ -1 then
    let truncated := nsec_diff.truncateTop h.right
    { seconds := (sec_diff - 1), nanos := truncated.addTop 1000000000 }
  else if h₁ : sec_diff.val < 0 ∧ nsec_diff.val ≥ 1 then
    let truncated := nsec_diff.truncateBottom h₁.right
    { seconds := (sec_diff + 1), nanos := (truncated.subBottom 1000000000) }
  else
    { seconds := sec_diff, nanos := nsec_diff }

instance : HSub Instant Instant Duration where
  hSub := Instant.sub

/--
Gets how much time elapsed since another `Instant` and returns a `Duration`.
-/
@[inline]
def since (instant : Instant) (since : Instant) : Duration :=
  Instant.sub since instant

end Instant

namespace Duration

/-- Returns a `Duration` representing the given number of second. -/
def ofSeconds (second : Second.Offset) : Duration :=
  { seconds := second, nanos := Bounded.LE.mk 0 (by decide) }

/-- Returns a `Duration` representing the given number of minute. -/
def ofMinutes (minute : Minute.Offset) : Duration :=
  { seconds := minute.toSeconds * 60, nanos := Bounded.LE.mk 0 (by decide) }

/-- Returns a `Duration` representing the given number of hour. -/
def ofHours (hour : Hour.Offset) : Duration :=
  { seconds := hour.toSeconds * 3600, nanos := Bounded.LE.mk 0 (by decide) }

end Duration
