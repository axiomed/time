/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time
import Time.Internal
import Lean.Data.Rat

namespace Std
namespace Time
open Lean Internal

set_option linter.all true

namespace Day

/--
`Ordinal` represents a bounded value for days, which ranges between 1 and 31.
-/
def Ordinal := Bounded.LE 1 31
  deriving Repr, BEq, LE, LT

instance [Le 1 n] [Le n 31] : OfNat Ordinal n where
  ofNat := Bounded.LE.mk (Int.ofNat n) (And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr Le.p))

instance { x y : Ordinal } : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance : Inhabited Ordinal where default := 1

/--
`Ordinal.OfYear` represents a bounded value for days, which ranges between 0 and 366 if the year
is a leap year or 365.
-/
def Ordinal.OfYear (leap : Bool) := Bounded.LE 1 (.ofNat (if leap then 366 else 365))

instance [Le 1 n] [Le n 365] : OfNat (Ordinal.OfYear leap) n where
  ofNat := Bounded.LE.mk (Int.ofNat n) (And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr (by have := Le.p (n := n) (m := 365); split <;> omega)))

instance : OfNat (Ordinal.OfYear true) 366 where
  ofNat := Bounded.LE.mk (Int.ofNat 366) (by decide)

instance : Inhabited (Ordinal.OfYear leap) where
  default := by
    refine ⟨1, And.intro (by decide) ?_⟩
    split <;> simp

/--
`Offset` represents an offset in days. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 86400
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 31 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds, if its 0 then its converted
to 1.
-/
@[inline]
def ofFin (data : Fin 32) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal

namespace Offset

/--
Convert `Day.Offset` into `Second.Offset`.
-/
@[inline]
def toSeconds (days : Offset) : Second.Offset :=
  days.mul 86400

/--
Convert `Day.Offset` into `Minute.Offset`.
-/
@[inline]
def toMinutes (days : Offset) : Minute.Offset :=
  days.mul 1440

/--
Convert `Day.Offset` into `Hour.Offset`.
-/
@[inline]
def toHours (days : Offset) : Hour.Offset :=
  days.mul 24

end Offset
end Day
end Time
end Std
