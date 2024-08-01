/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.UnitVal
import Time.Bounded
import Time.Classes
import Lean.Data.Rat
import Time.Time.Basic
import Time.Date.Unit.Day

namespace Date
open Lean Time

set_option linter.all true

namespace Month
/--
`Ordinal` represents a bounded value for months, which ranges between 1 and 12.
-/
def Ordinal := Bounded.LE 1 12
  deriving Repr, BEq, LE

instance [Le 1 n] [Le n 12] : OfNat Ordinal n where
  ofNat := Bounded.LE.mk (Int.ofNat n) (And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr Le.p))

instance : Inhabited Ordinal where default := 1

/--
`Offset` represents an offset in months. It is defined as an `Int`. It starts on the epoch.
-/
def Offset : Type := Int
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg

instance : OfNat Offset n := ⟨Int.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h: data ≥ 1 ∧ data ≤ 12 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Converts a `Ordinal` into a `Nat`.
-/
@[inline]
def toNat (month : Ordinal) : Nat :=
  Bounded.LE.toNat month

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
-/
@[inline]
def ofFin (data : Fin 13) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Transforms `Month.Ordinal` into `Second.Offset`.
-/
def toSeconds (leap : Bool) (month : Ordinal) : Second.Offset :=
  let daysAcc := #[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
  let time := daysAcc[month.toNat]! * 86400
  if leap && month.toNat ≥ 2
    then time + 86400
    else time

/--
Transforms `Month.Ordinal` into `Minute.Offset`.
-/
@[inline]
def toMinute (leap : Bool) (month : Ordinal) : Minute.Offset :=
  toSeconds leap month
  |>.div 60

/--
Transforms `Month.Ordinal` into `Hour.Offset`.
-/
@[inline]
def toHours (leap : Bool) (month : Ordinal) : Hour.Offset :=
  toMinute leap month
  |>.div 60

/--
Transforms `Month.Ordinal` into `Day.Offset`.
-/
@[inline]
def toDays (leap : Bool) (month : Ordinal) : Day.Offset :=
  toSeconds leap month
  |>.convert

/--
Size in days of each month if the year is not leap.
-/
@[inline]
def monthSizesNonLeap : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ], by simp⟩

/--
Size in days of each month.
-/
@[inline]
def monthSizes (isLeap : Bool) : { val : Array Day.Ordinal // val.size = 12 } :=
  ⟨#[ 31, if isLeap then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 ], by simp⟩

/--
Gets the number of
-/
def days (leap : Bool) (month : Ordinal) : Day.Ordinal :=
  if month.val = 2 then
    if leap then 29 else 28
  else by
    let ⟨months, p⟩ := monthSizesNonLeap
    let r : Fin 12 := (month.sub 1).toFin (by decide) (by decide)
    rw [← p] at r
    exact months.get r

/--
Transforms a `Day.Ordinal.OfYear` into a tuple of a `Month` and a `Day`.
-/
@[inline]
def ofOrdinal {leap : Bool} (ordinal : Day.Ordinal.OfYear leap) : Month.Ordinal × Day.Ordinal := Id.run do
  let mut cumulative : Fin 366 := ⟨0, by decide⟩

  for ((fin : Fin 12), days) in (monthSizes leap |>.val).mapIdx (·, ·) do
    if h: cumulative.val < ordinal.val ∧ ordinal.val ≤ cumulative.val + days.val then
      let bounded :=
        Bounded.LE.mk ordinal.val h |>.sub ↑↑cumulative
      let bounded : Bounded.LE 1 days.val := by
        simp [← Int.add_comm, Int.sub_self] at bounded
        rw [← Int.add_comm 1 (↑↑cumulative), Int.add_sub_assoc, Int.sub_self] at bounded
        exact bounded
      let month := Month.Ordinal.ofFin fin.succ
      let days := ⟨bounded.val, And.intro bounded.property.left (Int.le_trans bounded.property.right days.property.right)⟩
      return ⟨month, days⟩

    let h₁ := Int.toNat_lt (n := 366) (z := days.val) (Int.le_trans (by decide) days.property.left)
    let h₂ := h₁.mpr (Int.lt_of_le_of_lt days.property.right (by decide))
    cumulative := cumulative + ⟨days.toFin (by decide) (by decide), h₂⟩

  -- TODO: need to remove this
  panic! "Impossible"



end Ordinal
end Month
