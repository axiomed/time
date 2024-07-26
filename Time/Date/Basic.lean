import Time.Bounded

namespace Time.Date

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
  deriving Repr, Inhabited, BEq

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

def Weekday.ofNat? : Nat → Option Weekday
  | 0 => some .mon
  | 1 => some .tue
  | 2 => some .wed
  | 3 => some .thu
  | 4 => some .fri
  | 5 => some .sat
  | 6 => some .sun
  | _ => none

def Weekday.ofNat! (n: Nat) : Weekday :=
  match ofNat? n with
  | some res => res
  | none     => panic! "unwrap weekday"

def Weekday.ofDays : Int → Weekday :=
    ofNat! ∘ natOfDays
  where
    natOfDays (z: Int) : Nat :=
      if z ≥ -4 then ((z + 4) % 7).toNat
        else ((z + 5) % 7 + 6).toNat


/-- Represents a day of the year, independent of the year itself. It's defined as a bounded
natural number between 0 and 365. -/
def Ordinal (isLeap : Bool) := Bounded 1 (.ofNat (if isLeap then 367 else 366))

instance : Repr (Ordinal l) where
  reprPrec l p := reprPrec l.val p

/-- Make a ordinal out of a Nat and a proof -/
def Ordinal.mk {isLeap : Bool} (data : Nat) (proof : data ≥ 1 ∧ data < (if isLeap then 367 else 366) := by decide) : Ordinal isLeap :=
  Bounded.ofNat data proof

def Ordinal.force (data : Int) : Ordinal l :=
  Bounded.force data <| by simp; split; all_goals decide

/-- Represents a day of the month, independent of the month itself. -/
def Day := Bounded 1 32
  deriving Repr, BEq

@[inline]
def Day.mk (data : Nat) (proof : data ≥ 1 ∧ data < 32 := by decide) : Day :=
  Bounded.ofNat data proof

@[inline]
def Day.toNat : Day → Nat :=
  Bounded.toNat (h₀ := by decide)

@[inline]
def Day.ofFin (fin : Fin 31) : Day :=
  Bounded.ofFin fin
  |>.add 1

@[inline]
def Day.ofNatSucc (fin : Nat) : Day :=
  Day.ofFin (Fin.ofNat fin)

instance : OfNat Day 28 where ofNat := ⟨28, by decide⟩
instance : OfNat Day 29 where ofNat := ⟨29, by decide⟩
instance : OfNat Day 30 where ofNat := ⟨30, by decide⟩
instance : OfNat Day 31 where ofNat := ⟨31, by decide⟩

instance : Inhabited Day := ⟨1, by decide⟩

/-- Represents a month of the year. Similar to `Day`, it's defined as a bounded natural number,
this time between 1 and 13, inclusive -/
def Month := Bounded 1 13
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
@[inline]
def Month.mk (data : Nat) (proof : data ≥ 1 ∧ data < 13 := by decide) : Month :=
  Bounded.ofNat data proof

@[inline]
def Month.toNat (month : Month) : Nat :=
  Bounded.toNat month (by decide)

@[inline]
def Month.ofFin (fin : Fin 12) : Month :=
  Bounded.ofFin fin
  |>.add 1

@[inline]
def Month.ofNatSucc (fin : Nat) : Month :=
  Month.ofFin (Fin.ofNat fin)

/-- Array with the size of each month that can start on one and ends at 31. -/
def Month.monthSizesNonLeap : Array Day :=
  #[ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ]

/-- Array with the size of each month that can start on one and ends at 31. -/
def Month.monthSizes (isLeap : Bool) : { val : Array Day // val.size = 12 } :=
  ⟨#[ 31, if isLeap then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ], by simp⟩

/-- Returns the size of the month using the `isLeap` boolean and the month. -/
def Month.days (isLeap : Bool) (month : Month) : Day :=
  if month.val = 2
    then if isLeap then 29 else 28
    else Month.monthSizesNonLeap.get! (month.toNat - 1)

/-- Transforms a month into second. -/
def Month.toSecs (isLeap : Bool) (month : Month) : Nat :=
  let daysAcc := #[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]

  let time := daysAcc[month.toNat]! * 86400

  if isLeap && month.toNat ≥ 2
    then time + 86400
    else time

/-- Gets an `Ordinal` (Day of the Year) and transforms it into a Month and a Day. -/
def Month.ofOrdinal (isLeap: Bool) (ordinal: Ordinal isLeap) : (Month × Day) := Id.run do
    let val := ordinal.val.toNat
    let ⟨left, right⟩ := ordinal.property
    let left₁ : val ≥ 1 := (Int.le_toNat (by omega)).mpr left
    let ac := if isLeap then 1 else 0
    let feb : 28 + ac < 32 := by simp [ac]; cases isLeap; all_goals decide

    let mkRes (month : Month) (o : Nat) (proof : val - o ≥ 1 ∧ val - o < 32 := by omega) : (Month × Day) :=
      ⟨month, Day.mk (val - o) proof⟩

    if h : val ≤ 31 then mkRes 1 0
    else if h : val ≤ 59 + ac then mkRes 2 31
    else if h : val ≤ 90 + ac then mkRes 3 (59 + ac)
    else if h : val ≤ 120 + ac then mkRes 4 (90 + ac)
    else if h : val ≤ 151 + ac then mkRes 5 (120 + ac)
    else if h : val ≤ 181 + ac then mkRes 6 (151 + ac)
    else if h : val ≤ 212 + ac then mkRes 7 (181 + ac)
    else if h : val ≤ 242 + ac then mkRes 8 (212 + ac)
    else if h : val ≤ 273 + ac then mkRes 9 (242 + ac)
    else if h : val ≤ 304 + ac then mkRes 10 (273 + ac)
    else if h : val ≤ 334 + ac then mkRes 11 (304 + ac)
    else if h : val ≤ 365 + ac then mkRes 12 (334 + ac)
    else
    by
      let eq : (366 + if isLeap then 1 else 0) = (if isLeap then 367 else 366) := by cases isLeap; all_goals simp
      let h₀ := (Nat.not_le.mp h)
      let h₁ : (366 + ac) ≤ val := by rw [Nat.succ_add]; exact h₀
      let h₂ : (if isLeap then 367 else 366) ≤ val := by rw [←eq]; exact h₁
      let r : val < if isLeap = true then 367 else 366 := (Int.toNat_lt (Int.le_trans (by decide) left) (z := ordinal.val)).mpr right
      let h : val.succ ≤ val := Nat.le_trans r h₂
      let h₁ : ¬(val.succ ≤ val) := by omega
      contradiction

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

@[inline]
def Year.forceDay (year : Year) (month : Month)  (day : Day) : { x : Day // x.val ≤ (month.days year.isLeap).val } :=
  let max : Day := month.days year.isLeap
  if h : day.val > max.val
    then ⟨max, Int.le_refl max.val⟩
    else ⟨⟨day.val, day.property⟩, Int.not_lt.mp h⟩

/-- The range of CE years supported. -/
def Year.CE := Bounded 1 10000

/-- The range of BCE years supported. -/
def Year.BCE := Bounded 1 10001

inductive Era
  | CE
  | BCE

/-- Typeclass representing a date.  Any type implementing this class should provide methods to
retrieve the year and month.-/
class DateLike (α : Type) where
  year: α → Year
  month: α → Month
  day: α → Day
