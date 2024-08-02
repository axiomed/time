/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time
import Time.Date
import Time.DateTime
import Time.TimeZone.TimeZone

namespace TimeZone
open Time Date DateTime

/--
It stores a `Timestamp`, a `NaiveDateTime` and a `TimeZone`
-/
structure DateTime (tz : TimeZone) where
  private mk ::
  timestamp : Timestamp
  date : NaiveDateTime
  deriving Repr, BEq

def ZonedDateTime := Sigma DateTime

namespace DateTime

/--
Creates a new DateTime out of a `Timestamp`
-/
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=


/--
Getter for the `Year` inside of a `DateTime`
-/
@[inline]
def year (dt : DateTime tz) : Year.Offset :=
  dt.date.year

/--
Getter for the `Month` inside of a `DateTime`
-/
@[inline]
def month (dt : DateTime tz) : Month.Ordinal :=
  dt.date.month

/--
Getter for the `Day` inside of a `DateTime`
-/
@[inline]
def day (dt : DateTime tz) : Day.Ordinal :=
  dt.date.day

/--
Getter for the `Hour` inside of a `DateTime`
-/
@[inline]
def hour (dt : DateTime tz) : Hour.Ordinal :=
  dt.date.hour

/--
Getter for the `Minute` inside of a `DateTime`
-/
@[inline]
def minute (dt : DateTime tz) : Minute.Ordinal :=
  dt.date.minute

/--
Getter for the `Second` inside of a `DateTime`
-/
@[inline]
def second (dt : DateTime tz) : Second.Ordinal :=
  dt.date.second
