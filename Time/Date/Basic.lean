import Time.Date.Ordinal
import Time.Interval

namespace Time.Date

/-- Represents a day of the month, independent of the month itself. -/
def Day := Interval 1 32
  deriving Repr, BEq

def Day.mk (data: Nat) (proof: data ≥ 1 ∧ data < 32 := by decide) : Day := ⟨data, proof⟩

def Day.toNat (day: Day) : Nat :=
  day.val

/-- Converts a `Fin 31` representing a day index into a corresponding `Day`. This function is
useful for converting finite indices into actual days of the month. -/
def Day.ofFin (fin: Fin 31) : Day :=
  let gt_one_p := Nat.succ_le_succ (Nat.zero_le fin.val)
  let less_p := Nat.succ_le_succ fin.isLt
  ⟨fin.val.succ, And.intro gt_one_p less_p⟩

instance : OfNat Day 28 where ofNat := ⟨28, by decide⟩
instance : OfNat Day 29 where ofNat := ⟨29, by decide⟩
instance : OfNat Day 30 where ofNat := ⟨30, by decide⟩
instance : OfNat Day 31 where ofNat := ⟨31, by decide⟩

instance : Inhabited Day := ⟨1, by decide⟩

/-- Represents a month of the year. Similar to `Day`, it's defined as a bounded natural number,
this time between 1 and 13, inclusive -/
def Month := Interval 1 13
  deriving Repr, BEq

instance : OfNat Month 1 where ofNat := ⟨1, by decide⟩
instance : OfNat Month 2 where ofNat := ⟨2, by decide⟩
instance : OfNat Month 3 where ofNat := ⟨3, by decide⟩
instance : OfNat Month 4 where ofNat := ⟨4, by decide⟩
instance : OfNat Month 5 where ofNat := ⟨5, by decide⟩
instance : OfNat Month 6 where ofNat := ⟨6, by decide⟩
instance : OfNat Month 7 where ofNat := ⟨7, by decide⟩
instance : OfNat Month 8 where ofNat := ⟨8, by decide⟩
instance : OfNat Month 9 where ofNat := ⟨9, by decide⟩
instance : OfNat Month 10 where ofNat := ⟨10, by decide⟩
instance : OfNat Month 11 where ofNat := ⟨11, by decide⟩
instance : OfNat Month 12 where ofNat := ⟨12, by decide⟩

instance : Inhabited Month := ⟨1, by decide⟩

/-- Constructs a `Month` from a `Nat` within the valid range of [1, 12]. This function ensures that
the input is within the valid range for a month. -/
def Month.mk (data: Nat) (proof: data ≥ 1 ∧ data < 13 := by decide) : Month := ⟨data, proof⟩

/-- Converts a `Fin 12` representing a month index into a corresponding `Month`. This function is
 useful for converting finite indices into actual months.-/
def Month.ofFin (fin: Fin 12) : Month :=
  let gt_one_p := Nat.succ_le_succ (Nat.zero_le fin.val)
  let less_p := Nat.succ_le_succ fin.isLt
  ⟨fin.val.succ, And.intro gt_one_p less_p⟩

def Month.toNat (month: Month) : Nat :=
  month.val

/-- Array with the size of each month that can start on one and ends at 31. -/
def Month.monthSizesNonLeap : Array Day :=
  #[ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ]

/-- Array with the size of each month that can start on one and ends at 31. -/
def Month.monthSizes (isLeap: Bool) : Array Day :=
  #[ 31, if isLeap then 28 else 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ]

/-- Returns the size of the month using the `isLeap` boolean and the month. -/
def Month.days (isLeap: Bool) (month: Month) : Day :=
  if month.val = 2
    then if isLeap then 29 else 28
    else Month.monthSizesNonLeap.get! (month.val - 1)

/-- Transforms a month into second -/
def Month.toSecs (isLeap: Bool) (month: Month) : Nat :=
  let daysAcc := #[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]

  let time := daysAcc[month.val]! * 86400

  if isLeap && month.val ≥ 2
    then time + 86400
    else time

/-- Calculates the mod of the value to force it to be bellow 13 and then forces it to one if its lower
than one to create a `Month` -/
def Month.forceBounds (data: Nat) : Month :=
  let fin := Fin.byMod data 13
  if h: fin.val ≥ 1
    then Month.mk fin.val (And.intro h fin.isLt)
    else Month.mk 1 (by decide)

/-- Gets an `Ordinal` (Day of the Year) and transforms it into a Month and a Day. -/
def Month.ofOrdinal (isLeap: Bool) (ordinal: Ordinal isLeap) : (Month × Day) := Id.run do
  let mut cumulative : Fin 366 := ⟨0, by decide⟩

  for (fin, ⟨days, proof⟩) in (Month.monthSizes isLeap).mapIdx (·, ·) do
    let days : Fin 32 := ⟨days, proof.right⟩
    if h: ordinal.val > cumulative.val ∧ ordinal.val ≤ cumulative.val + days.val then
      let bounded := Interval.addMax (Interval.ofFin fin) 1
      let t : Fin 32 := Fin.ofBoundaries h.left h.right (by decide)
      let day := if h : t > 0
        then Day.mk t (And.intro h t.isLt)
        else Day.mk 1
      return (bounded, day)
    cumulative := cumulative + ⟨days.val, Nat.lt_trans proof.right (by decide)⟩

  return Inhabited.default

/-- Represents a year in proleptic gregorian calendar. -/
def Year := Int
  deriving Repr, BEq, Inhabited, ToString

instance : OfNat Year n where ofNat := Int.ofNat n

@[inline]
def Year.toInt (x: Year) : Int := x

/-- Predicate indicating whether a year is a leap year.  A leap year is divisible by 4 but not by
100, except if it's also divisible by 400.  This function checks if a given year satisfies the
conditions for a leap year.-/
@[inline]
abbrev Year.isLeap (y : Year) : Prop :=
  let y : Int := y
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
