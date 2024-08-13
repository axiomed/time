/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Basic

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a specific point in time, including hours, minutes, seconds, and nanoseconds.
-/
structure LocalTime where
  /--
  `Hour` component of the `LocalTime`
  -/
  hour : Hour.Ordinal

  /--
  `Minute` component of the `LocalTime`
  -/
  minute : Minute.Ordinal

  /--
  `Second` component of the `LocalTime`
  -/
  second : Second.Ordinal

  /--
  `Nanoseconds` component of the `LocalTime`
  -/
  nano : Nanosecond.Ordinal
  deriving Repr, Inhabited, BEq

namespace LocalTime

/--
Creates a `LocalTime` value from hours, minutes, and seconds, setting nanoseconds to zero.
-/
def ofHourMinuteSeconds (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal) : LocalTime :=
  ⟨hour, minute, second, 0⟩

/--
Converts a `LocalTime` value to the total number of seconds since midnight.
-/
def toNanoseconds (time : LocalTime) : Nanosecond.Offset :=
  let secs :=
    time.hour.toOffset.toSeconds +
    time.minute.toOffset.toSeconds +
    time.second.toOffset
  let nanos := secs.mul 1000000000
  UnitVal.mk (nanos.val + time.nano.val)

/--
Converts a `LocalTime` value to the total number of seconds since midnight.
-/
def toSeconds (time : LocalTime) : Second.Offset :=
  time.hour.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.toOffset

/--
Converts a `LocalTime` value to the total number of minutes since midnight.
-/
def toMinutes (time : LocalTime) : Minute.Offset :=
  time.hour.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.toOffset.toMinutes

end LocalTime
end Time
end Std
