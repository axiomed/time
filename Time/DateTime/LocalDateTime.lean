/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Date
import Time.Time
import Time.Internal
import Time.DateTime.Timestamp

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Date time format with Year, Month, Day, Hour, Minute, Seconds and Nanoseconds.
-/
structure LocalDateTime where
  /--
  The `Date` component of a `LocalDateTime`
  -/
  date : LocalDate

  /--
  The `Time` component of a `LocalDateTime`
  -/
  time : LocalTime
  deriving Repr, Inhabited

namespace LocalDateTime

/--
Converts a `LocalDateTime` into a `Std.Time.Timestamp`
-/
def toUTCTimestamp (dt : LocalDateTime) : Timestamp :=
  let days := dt.date.toDaysSinceUNIXEpoch
  let nanos : Nanosecond.Offset := days.toSeconds + dt.time.toSeconds |>.mul 1000000000
  let nanos := nanos.val + dt.time.nano.val
  Timestamp.ofNanoseconds (UnitVal.mk nanos)

/--
Converts a UNIX `Timestamp` into a `LocalDateTime`.
-/
def ofUTCTimestamp (stamp : Timestamp) : LocalDateTime := Id.run do
  let leapYearEpoch := 11017
  let daysPer400Y := 365 * 400 + 97
  let daysPer100Y := 365 * 100 + 24
  let daysPer4Y := 365 * 4 + 1

  let nanos := stamp.toNanoseconds
  let secs : Second.Offset := nanos.ediv 1000000000
  let daysSinceEpoch : Day.Offset := secs.ediv 86400
  let boundedDaysSinceEpoch := daysSinceEpoch

  let mut rawDays := boundedDaysSinceEpoch - leapYearEpoch
  let mut rem := Bounded.LE.byMod secs.val 86400 (by decide)

  let ⟨remSecs, days⟩ :=
    if h : rem.val ≤ -1 then
      let remSecs := rem.truncateTop h
      let remSecs : Bounded.LE 1 86399 := remSecs.add 86400
      let rawDays := rawDays - 1
      (remSecs.expandBottom (by decide), rawDays)
    else
      let h := rem.truncateBottom (Int.not_le.mp h)
      (h, rawDays)

  let mut quadracentennialCycles := days / daysPer400Y;
  let mut remDays := days.val % daysPer400Y.val;

  if remDays < 0 then
    remDays := remDays + daysPer400Y.val
    quadracentennialCycles := quadracentennialCycles - 1

  let mut centenialCycles := remDays / daysPer100Y;

  if centenialCycles = 4 then
    centenialCycles := centenialCycles - 1

  remDays := remDays - centenialCycles * daysPer100Y
  let mut quadrennialCycles := remDays / daysPer4Y;

  if quadrennialCycles = 25 then
    quadrennialCycles := quadrennialCycles - 1

  remDays := remDays - quadrennialCycles * daysPer4Y
  let mut remYears := remDays / 365;

  if remYears = 4 then
    remYears := remYears - 1

  remDays := remDays - remYears * 365

  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles.val
  let months := [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
  let mut mon : Fin 13 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat (Int.toNat remDays)

  let hmon ←
    if h₁ : mon.val > 10
      then do
        year := year + 1
        pure (Month.Ordinal.ofNat (mon.val - 10) (by omega))
      else
        pure (Month.Ordinal.ofNat (mon.val + 2) (by omega))

  let second : Bounded.LE 0 59 := remSecs.emod 60 (by decide)
  let minute : Bounded.LE 0 59 := (remSecs.ediv 60 (by decide)).emod 60 (by decide)
  let hour : Bounded.LE 0 23 := remSecs.ediv 3600 (by decide)
  let nano : Bounded.LE 0 999999999 := Bounded.LE.byEmod nanos.val 1000000000 (by decide)

  return {
    date := LocalDate.clip year hmon (Day.Ordinal.ofFin (Fin.succ mday))
    time := LocalTime.mk (hour.expandTop (by decide)) minute (second.expandTop (by decide)) nano
  }

/--
Getter for the `Year` inside of a `LocalDateTime`
-/
@[inline]
def year (dt : LocalDateTime) : Year.Offset :=
  dt.date.year

/--
Getter for the `Month` inside of a `LocalDateTime`
-/
@[inline]
def month (dt : LocalDateTime) : Month.Ordinal :=
  dt.date.month

/--
Getter for the `Day` inside of a `LocalDateTime`
-/
@[inline]
def day (dt : LocalDateTime) : Day.Ordinal :=
  dt.date.day

/--
Getter for the `Hour` inside of a `LocalDateTime`
-/
@[inline]
def hour (dt : LocalDateTime) : Hour.Ordinal :=
  dt.time.hour

/--
Getter for the `Minute` inside of a `LocalDateTime`
-/
@[inline]
def minute (dt : LocalDateTime) : Minute.Ordinal :=
  dt.time.minute

/--
Getter for the `Second` inside of a `LocalDateTime`
-/
@[inline]
def second (dt : LocalDateTime) : Second.Ordinal :=
  dt.time.second

/--
Getter for the `Second` inside of a `LocalDateTime`
-/
@[inline]
def nanoseconds (dt : LocalDateTime) : Nanosecond.Ordinal :=
  dt.time.nano

end LocalDateTime
end Time
end Std
