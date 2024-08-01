/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.UnitVal
import Time.Date.Basic
import Time.Date.Scalar

namespace Date

/--
Date in YMD format.
-/
structure Date where
  years : Year.Offset
  months : Month.Ordinal
  days : Day.Ordinal
  valid : days ≤ (months.days years.isLeap)
  deriving Repr, BEq

namespace Date

/--
Force the date to be valid.
-/
def force (years : Year.Offset) (months : Month.Ordinal) (days : Day.Ordinal) : Date :=
  let ⟨days, valid⟩ := years.forceDay months days
  Date.mk years months days valid

/--
Returns the `Weekday` of a `Date`.
-/
def weekday (date: Date) : Weekday :=
  let q := date.days.toInt
  let m := date.months.toInt
  let y := date.years.toInt

  let y := if m < 2 then y - 1 else y
  let m := if m < 2 then m + 12 else m

  let k := y % 100
  let j := y / 100
  let part := q + (13 * (m + 1)) / 5 + k + (k / 4)
  let h :=  if y ≥ 1582 then part + (j/4) - 2*j else part + 5 - j
  let d := (h + 5) % 7

  .ofFin ⟨d.toNat % 7, Nat.mod_lt d.toNat (by decide)⟩

/--
Returns the `Weekday` of a `Date` using Zeller's Congruence for the Julian calendar.
-/
def weekdayJulian (date : Date) : Weekday :=
  let month := date.months.toInt
  let years := date.years.toInt

  let q := date.days.toInt
  let m := if month < 3 then month + 12 else month
  let y := if month < 3 then years - 1 else years

  let k := y % 100
  let j := y / 100

  let h := (q + (13 * (m + 1)) / 5 + k + (k / 4) + 5 - j) % 7
  let d := (h + 5 - 1) % 7

  .ofFin ⟨d.toNat % 7, Nat.mod_lt d.toNat (by decide)⟩

/--
Returns the `Scalar` starting from the UNIX epoch.
-/
def toScalar (date : Date) : Scalar :=
  let y : Int := if date.months.toInt > 2 then date.years else date.years.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := date.months.toInt
  let d : Int := date.days.toInt
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy

  ⟨.ofInt (era * 146097 + doe - 719468)⟩

/--
Creates a new `Date` from a `Scalar` that begins on the epoch.
-/
def ofScalar (z: Scalar) : Date :=
  let z := z.days.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp: Int := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)

  .force y (.force m (by decide)) (.force (d + 1) (by decide))

instance : HAdd Date Day.Offset Date where
  hAdd date days :=  ofScalar (toScalar date + ⟨days⟩)

instance : HAdd Date Scalar Date where
  hAdd date days := ofScalar (toScalar date + days)
