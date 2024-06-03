import Time.Bounded
import Time.Epoch

namespace Time

/-! Implementation of Date-like structures. Using the proleptic Gregorian calendar. -/

/-- Defines the enumeration for days of the week. Each variant corresponds to a day of the week,
from Monday to Sunday. -/
inductive Weekday
  | mon
  | tue
  | wed
  | thu
  | fri
  | sat
  | sun
  deriving Repr

/-- Converts a `Fin 7` representing a day index into a corresponding `Weekday`. This function is
useful for mapping numerical representations to days of the week. -/
def Weekday.ofFin : Fin 7 → Weekday
  | 0 => .mon
  | 1 => .tue
  | 2 => .wed
  | 3 => .thu
  | 4 => .fri
  | 5 => .sat
  | 6 => .sun

/-- Represents a day of the year, independent of the year itself. It's defined as a bounded
natural number between 0 and 365. -/
abbrev Ordinal (isLeap: Bool) := Nat.Bounded 1 (if isLeap then 367 else 366)

def Ordinal.mk (data: Nat) (proof: data ≥ 1 ∧ data < (if isLeap then 367 else 366) := by decide) : Ordinal isLeap :=
  ⟨data, proof⟩

/-- Represents a day of the month, independent of the month itself. It's defined as a bounded
natural number between 1 and 31. -/
abbrev Day := Nat.Bounded 1 32

instance : Inhabited Day :=
  ⟨1, by decide⟩

/-- Constructs a `Day` from a `Nat` within the valid range of [1, 31]. This function ensures that
 the input is within the valid range for a day. -/
def Day.mk (data: Nat) (proof: data ≥ 1 ∧ data < 32 := by decide) : Day := ⟨data, proof⟩

/-- Converts a `Fin 31` representing a day index into a corresponding `Day`. This function is
useful for converting finite indices into actual days of the month. -/
def Day.ofFin (fin: Fin 31) : Day :=
  let gt_one_p := Nat.succ_le_succ (Nat.zero_le fin.val)
  let less_p := Nat.succ_le_succ fin.isLt
  ⟨fin.val.succ, And.intro gt_one_p less_p⟩

/-- Represents a month of the year. Similar to `Day`, it's defined as a bounded natural number,
this time between 1 and 13, inclusive -/
abbrev Month := Nat.Bounded 1 13

instance : Inhabited Month :=
  ⟨1, by decide⟩

/-- Constructs a `Month` from a `Nat` within the valid range of [1, 12]. This function ensures that
the input is within the valid range for a month. -/
def Month.mk (data: Nat) (proof: data ≥ 1 ∧ data < 13 := by decide) : Month := ⟨data, proof⟩

/-- Calculates the mod of the value to force it to be bellow 13 and then forces it to one if its lower
than one to create a `Month` -/
def Month.forceBounds (data: Nat) : Month :=
  let fin := Fin.byMod data 13
  if h: fin ≥ 1
    then Month.mk fin (And.intro h fin.isLt)
    else Month.mk 1 (by decide)

/-- Array with the size of each month that can start on one and ends at 31. It depends on the `leap`
parameter because it needs to calculate if Febuary will have one day because of the Leap Year. -/
def Month.monthSizes (leap: Bool) : Array (Nat.Bounded 1 32) :=
  #[ ⟨31, by decide⟩
   , ⟨28 + if leap then 1 else 0, by if h : leap then simp [h] else simp [h]⟩
   , ⟨31, by decide⟩
   , ⟨30, by decide⟩
   , ⟨31, by decide⟩
   , ⟨30, by decide⟩
   , ⟨31, by decide⟩
   , ⟨31, by decide⟩
   , ⟨30, by decide⟩
   , ⟨31, by decide⟩
   , ⟨30, by decide⟩
   , ⟨31, by decide⟩
   ]

/-- Returns the size of the month using the `isLeap` boolean and the month. -/
def Month.days (isLeap: Bool) (month: Month) : Nat :=
  if month.val = 2
    then if isLeap then 29 else 28
    else if month.val ≤ 7 then 30 + (month.val % 2)
    else 31 - (month.val % 2)

/-- Transforms a month into second -/
def Month.toSecs (isLeap: Bool) (month: Month) : Nat :=
  let secsThroughMonths :=
    [ 0, 31*86400, 59*86400, 90*86400
    , 120*86400, 151*86400, 181*86400, 212*86400
    , 243*86400, 273*86400, 304*86400, 334*86400]

  let time := secsThroughMonths[month.val]!

  if isLeap && month.val ≥ 2
    then time + 86400
    else time

/-- Gets an `Ordinal` (Day of the Year) and transforms it into a Month and a Day. -/
def Month.ofOrdinal (isLeap: Bool) (ordinal: Ordinal isLeap) : (Month × Day) := Id.run do
  let mut cumulative : Fin 366 := ⟨0, by decide⟩

  for (fin, ⟨days, proof⟩) in (Month.monthSizes isLeap).mapIdx (·, ·) do
    let days : Fin 32 := ⟨days, proof.right⟩
    if h: ordinal.val > cumulative.val ∧ ordinal.val ≤ cumulative.val + days.val then
      let bounded := Nat.Bounded.addMax (Nat.Bounded.ofFin fin) 1
      let t : Fin 32 := Fin.ofBoundaries h.left h.right (by decide)
      let day := if h : t > 0
        then Day.mk t (And.intro h t.isLt)
        else Day.mk 1
      return (bounded, day)
    cumulative := cumulative + ⟨days.val, Nat.lt_trans proof.right (by decide)⟩

  -- TODO: need to remove this
  panic! "Impossible"

/-- Converts a `Fin 12` representing a month index into a corresponding `Month`. This function is
 useful for converting finite indices into actual months.-/
def Month.ofFin (fin: Fin 12) : Month :=
  let gt_one_p := Nat.succ_le_succ (Nat.zero_le fin.val)
  let less_p := Nat.succ_le_succ fin.isLt
  ⟨fin.val.succ, And.intro gt_one_p less_p⟩

/-- Represents a year within the range from 0 to 9999.  It's defined as a simple natural number.-/
abbrev Year := Nat

/-- Predicate indicating whether a year is a leap year.  A leap year is divisible by 4 but not by
100, except if it's also divisible by 400.  This function checks if a given year satisfies the
conditions for a leap year.-/
@[inline]
abbrev Year.isLeap (y : Year) : Prop :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

/-- Year that can contain BC dates -/
abbrev HistoricalYear := Int

/-- Predicate indicating whether a historical year is a leap year. --/
@[inline]
abbrev HistoricalYear.isLeap (y : HistoricalYear) : Prop :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

/-- Typeclass representing a date.  Any type implementing this class should provide methods to
retrieve the year and month.-/
class DateLike (α : Type) where
  year: α → Year
  month: α → Month
  day: α → Day

  setYear : α → Year → α
  setMonth : α → Month → α
  setDay : α → Day → α

/-- Date without time offset like UTC. -/
structure Date where
  year: Year
  month: Month
  day: Day
  deriving Repr, BEq, Inhabited

instance : DateLike Date where
  year date := date.year
  month date := date.month
  day date := date.day

  setYear date value := { date with year := value }
  setMonth date value := { date with month := value }
  setDay date value := { date with day := value }

/-- Constructs a `Date` from a number of days since an epoch. -/
def Date.ofDays (days : Int) : Date :=
  let y := (10000 * days + 14780) / 3652425
  let ddd := days - (365 * y + y / 4 - y / 100 + y / 400)
  let (y, ddd) :=
    if ddd < 0 then
      let y := y - 1
      let ddd := days - (365 * y + y / 4 - y / 100 + y / 400)
      (y, ddd)
    else
      (y, ddd)
  let mi := (100 * ddd + 52) / 3060
  let mm := Fin.byMod (mi + 2).toNat 12
  let y := y + (mi + 2) / 12
  let dd := ddd - (mi * 306 + 5) / 10
  let dd := Fin.byMod dd.toNat 31
  Date.mk y.toNat (Month.ofFin mm) (Day.ofFin dd)

/-- Creates a `Date` from given year, month, and day values. This function constructs a complete
date using the provided components. -/
def Date.ofYMD : Year → Month → Day → Date :=
  Date.mk

/-- Creates a new `Date` from a year and an ordinal day (day of the year). This function is useful
for converting day-of-year values to regular dates. -/
def Date.ofYO (year: Year) (day: Ordinal year.isLeap) : Date :=
  let (month, day) := Month.ofOrdinal year.isLeap day
  Date.mk year month day

/-- Converts a `Date` to the number of days since an epoch. -/
def Date.toDays (date: Date) : Int :=
  let m := ((date.month.val : Int) + 9) % 12
  let y := (date.year : Int) - m / 10
  365 * y + (y / 4) - (y / 100) + (y / 400) + (m * 306 + 5) / 10 + ((date.day.val : Int)- 1)

/-- Calculates the `Weekday` for a given `Date`.  -/
def Date.weekday (date: Date) : Weekday :=
  let q := date.day.val
  let m := date.month.val
  let y := date.year

  -- In the algorithm May = 3 and January = 13, February = 14.
  let y := if m < 2 then y - 1 else y
  let m := if m < 2 then m + 12 else m

  let k := y % 100
  let j := y / 100
  let part := q + (13 * (m + 1)) / 5 + k + (k / 4)
  let h :=  if y ≥ 1582 then part + (j/4) - 2*j else part + 5 - j
  let d := (h + 5) % 7
  Weekday.ofFin (⟨d % 7, Nat.mod_lt d (by decide)⟩)

/-- Calculates the number of days from the civil epoch (1970-01-01) to a given `Date`. -/
def Date.civilFromDate (date: Date) : Int :=
  let y : Int := if date.month.val > 2 then date.year else date.year - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.val
  let d : Int := date.day.val
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  (era * 146097 + doe - 719468)

/-- Converts a number of days since the civil epoch to a `Date`. This function translates a day count
into a full calendar date, accounting for leap years and month lengths. -/
def Date.dateFromCivil (z: Int) : Date :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp: Int := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)
  { year := Int.toNat y,
    month := Month.forceBounds m.toNat,
    day := Day.ofFin (Fin.byMod d.toNat 31)
  }

/-- Subtracts a given number of days from a `Date` and returns the resulting `Date`.
This function helps in calculating past dates by subtracting day counts. -/
@[inline]
def Date.subDays (date: Date) (days: Int) : Date :=
  Date.dateFromCivil (date.civilFromDate - days)

/-- Adds a given number of days to a `Date` and returns the resulting `Date`. -/
@[inline]
def Date.addDays (date: Date) (days: Int) : Date :=
  Date.dateFromCivil (date.civilFromDate + days)

/-- Converts a number of days since the civil epoch to the corresponding weekday. This function
translates a day count into a day of the week. -/
def weekdayFromDays (z: Int) : Nat :=
  if z ≥ -4
    then ((z + 4) % 7).toNat
    else ((z + 5) % 7 + 6).toNat

/-- Converts a `Date` to the Epoch representation. This function calculates the number of second
from a `Date` to the Unix epoch, accounting for leap years and month lengths. -/
def Date.toEpoch (date: Date) (_: date.year ≥ 1970) : Epoch :=
  let z := Date.civilFromDate date
  let ns := z.toNat * 86400
  Fin.byMod ns 253402300800
