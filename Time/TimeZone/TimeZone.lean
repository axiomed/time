/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Unit.Basic
import Time.TimeZone.Basic

namespace TimeZone
open Time

/--
An enumeration representing different time zones.
-/
structure TimeZone where
  offset : Offset
  name : String

/--
A zeroed `Timezone` representing UTC (no offset).
-/
def UTC (name : String) : TimeZone :=
  TimeZone.mk (Offset.zero) name

/--
A zeroed `Timezone` representing GMT (no offset).
-/
def GMT (name : String) : TimeZone :=
  TimeZone.mk (Offset.zero) name

/--
Creates a `Timestamp` from a given number of hour.
-/
def ofHours (name : String) (n: Hour.Offset) : TimeZone :=
  TimeZone.mk (Offset.ofHours n) name

/--
Creates a `Timestamp` from a given number of second.
-/
def ofSeconds (name : String) (n: Second.Offset) : TimeZone :=
  TimeZone.mk (Offset.ofSeconds n) name
