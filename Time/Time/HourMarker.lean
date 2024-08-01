/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Basic

namespace Time

/--
`HourMarker` represents the two 12-hour periods of the day: `am` for hours between 12:00 AM and
11:59 AM, and `pm` for hours between 12:00 PM and 11:59 PM.
-/
inductive HourMarker
  | am
  | pm

/--
Converts a 12-hour clock time to a 24-hour clock time based on the `HourMarker`.
-/
def HourMarker.toAbsolute (marker : HourMarker) (time : Hour.Ordinal) (h₀ : time.toInt ≤ 12) : Hour.Ordinal :=
  match marker with
  | .am => time
  | .pm => Bounded.LE.mk (time.toInt + 12) (And.intro (Int.add_le_add (c := 0) time.property.left (by decide)) (Int.add_le_add_right h₀ 12))
