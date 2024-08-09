/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.DateTime
import Time.Zoned.TimeZone
import Time.Zoned.ZoneRules

namespace Std
namespace Time

/--
It stores a `Timestamp`, a `LocalDateTime` and a `TimeZone`
-/
structure DateTime (tz : TimeZone) where
  private mk ::
  timestamp : Timestamp
  date : Thunk LocalDateTime

instance : Inhabited (DateTime tz) where
  default := ⟨Inhabited.default, Thunk.mk λ_ => Inhabited.default⟩

namespace DateTime

/--
Creates a new `DateTime` out of a `Timestamp`
-/
@[inline]
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=
  DateTime.mk tm (Thunk.mk <| λ_ => (tm + tz.toSeconds).toLocalDateTime)

/--
Creates a new `Timestamp` out of a `DateTime`
-/
@[inline]
def toTimestamp (date : DateTime tz) : Timestamp :=
  date.timestamp

/--
Changes the `TimeZone` to a new one.
-/
@[inline]
def convertTimeZone (date : DateTime tz) (tz₁ : TimeZone) : DateTime tz₁ :=
  ofTimestamp (date.toTimestamp) tz₁

/--
Creates a new DateTime out of a `LocalDateTime`
-/
@[inline]
def ofLocalDateTime (date : LocalDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := date.toTimestamp - tz.toSeconds
  DateTime.mk tm date

/--
Getter for the `Year` inside of a `DateTime`
-/
@[inline]
def year (dt : DateTime tz) : Year.Offset :=
  dt.date.get.year

/--
Getter for the `Month` inside of a `DateTime`
-/
@[inline]
def month (dt : DateTime tz) : Month.Ordinal :=
  dt.date.get.month

/--
Getter for the `Day` inside of a `DateTime`
-/
@[inline]
def day (dt : DateTime tz) : Day.Ordinal :=
  dt.date.get.day

/--
Getter for the `Hour` inside of a `DateTime`
-/
@[inline]
def hour (dt : DateTime tz) : Hour.Ordinal :=
  dt.date.get.hour

/--
Getter for the `Minute` inside of a `DateTime`
-/
@[inline]
def minute (dt : DateTime tz) : Minute.Ordinal :=
  dt.date.get.minute

/--
Getter for the `Second` inside of a `DateTime`
-/
@[inline]
def second (dt : DateTime tz) : Second.Ordinal :=
  dt.date.get.second

/--
Getter for the `Milliseconds` inside of a `DateTime`
-/
@[inline]
def milliseconds (dt : DateTime tz) : Millisecond.Ordinal :=
  dt.date.get.time.nano.toMillisecond
/--
Gets the `Weekday` of a DateTime.
-/
@[inline]
def weekday (dt : DateTime tz) : Weekday :=
  dt.date.get.date.weekday

end DateTime
end Time
end Std
