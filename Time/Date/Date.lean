import Time.Date.Basic

namespace Time.Date

/-- Date without time offset like UTC. -/
structure YMD where
  year: Year
  month: Month
  day: Day
  valid: day.val ≤ (month.days year.isLeap).val
  deriving Repr, BEq

instance : DateLike YMD where
  year date := date.year
  month date := date.month
  day date := date.day

def YMD.isValid (date: YMD) : Prop :=
  date.day.val ≤ (date.month.days date.year.isLeap).val

/-- Creates a `YMD` from given year, month, and day values. This function constructs a complete
date using the provided components. -/
def YMD.ofYMD (year : Year) (month : Month) (day : Day) : YMD :=
    let max : Day := month.days year.isLeap
    let ⟨day, h⟩ : { x : Day // x.val ≤ max.val } :=
      if h : day.val > max.val
        then ⟨max, Int.le_refl max.val⟩
        else ⟨⟨day.val, day.property⟩, Int.not_lt.mp h⟩
    YMD.mk year month day h

/-- Constructs a `YMD` from a number of days since an epoch. -/
def YMD.ofDays (days : Int) : YMD :=
  let y := (10000 * days + 14780) / 3652425
  let ddd := days - (365 * y + y / 4 - y / 100 + y / 400)
  let (y, ddd) :=
    if ddd < 0
    then (y - 1, days - (365 * y + y / 4 - y / 100 + y / 400))
    else (y, ddd)
  let mi := (100 * ddd + 52) / 3060
  let mm : Fin 12 := Fin.ofNat (mi + 2).toNat
  let year := y + (mi + 2) / 12
  let dd := ddd - (mi * 306 + 5) / 10
  let dd : Fin 31 := Fin.ofNat dd.toNat
  let month := Month.ofFin mm
  let day := Day.ofFin dd
  let ⟨day, valid⟩ := Year.forceDay year month day
  .mk year month day valid

/-- Converts a `YMD` to the number of days since an epoch. -/
def YMD.toDays (date: YMD) : Int :=
  let m := ((date.month.val) + 9) % 12
  let y := date.year.toInt - m / 10
  365 * y + (y / 4) - (y / 100) + (y / 400) + (m * 306 + 5) / 10 + (date.day.val - 1)

/-- Creates a new `YMD` from a year and an ordinal day (day of the year). This function is useful
for converting day-of-year values to regular dates. -/
def YMD.ofOrdinal (year: Year) (day: Ordinal year.isLeap) : YMD :=
  let (month, day) := Month.ofOrdinal year.isLeap day
  let ⟨day, valid⟩ := Year.forceDay year month day
  .mk year month day valid

/-- Calculates the `Weekday` for a given `YMD`.  -/
def YMD.weekday (date: YMD) : Weekday :=
  let q := date.day.val
  let m := date.month.val
  let y := date.year

  -- In the algorithm May = 3 and January = 13, February = 14.
  let y := if m < 2 then y.toInt - 1 else y
  let m := if m < 2 then m + 12 else m

  let k := y % 100
  let j := y / 100
  let part := q + (13 * (m + 1)) / 5 + k + (k / 4)
  let h :=  if y ≥ 1582 then part + (j/4) - 2*j else part + 5 - j
  let d := (h + 5) % 7

  Weekday.ofFin (Fin.ofNat d.toNat)

/-- Calculates the number of days from the civil epoch (1970-01-01) to a given `YMD`. -/
def YMD.civilFromDate (date : YMD) : Int :=
  let y : Int := if date.month.val > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.val
  let d : Int := date.day.val
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  (era * 146097 + doe - 719468)

/-- Converts a number of days since the civil epoch to a `YMD`. This function translates a day count
into a full calendar date, accounting for leap years and month lengths. -/
def YMD.dateFromCivil (z: Int) : YMD :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp: Int := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5
  let m := mp + (if mp < 10 then 2 else -10)
  let year := y + (if m <= 2 then 1 else 0)
  let month := Month.ofNatSucc m.toNat
  let day := Day.ofNatSucc d.toNat
  let ⟨day, valid⟩ := Year.forceDay year month day
  .mk year month day valid

/-- Subtracts a given number of days from a `YMD` and returns the resulting `YMD`.
This function helps in calculating past dates by subtracting day counts. -/
@[inline]
def YMD.subDays (date: YMD) (days: Int) : YMD :=
  dateFromCivil (date.civilFromDate - days)

/-- Adds a given number of days to a `YMD` and returns the resulting `YMD`. -/
@[inline]
def YMD.addDays (date: YMD) (days: Int) : YMD :=
  dateFromCivil (date.civilFromDate + days)
