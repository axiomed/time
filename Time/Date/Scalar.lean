/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.UnitVal
import Time.Date.Basic

namespace Date

/--
`Scalar` represents a date offset, using the number of days as the underlying unit.
-/
structure Scalar where
  days : Day.Offset
  deriving Repr, BEq, Inhabited

instance : Add Scalar where add x y := ⟨x.days + y.days⟩
instance : Sub Scalar where sub x y := ⟨x.days - y.days⟩
instance : Mul Scalar where mul x y := ⟨x.days * y.days⟩
instance : Div Scalar where div x y := ⟨x.days / y.days⟩
instance : Neg Scalar where neg x := ⟨-x.days⟩

namespace Scalar

/--
Creates a `Scalar` from a given number of days.
-/
def ofDays (days : Int) : Scalar :=
  ⟨UnitVal.ofInt days⟩

/--
Retrieves the number of days from a `Scalar`.
-/
def toDays (scalar : Scalar) : Int :=
  scalar.days.val

/--
Adds a specified number of days to the `Scalar`, returning a new `Scalar`.
-/
def addDays (scalar : Scalar) (days : Day.Offset) : Scalar :=
  ⟨scalar.days + days⟩

/--
Subtracts a specified number of days from the `Scalar`, returning a new `Scalar`.
-/
def subDays (scalar : Scalar) (days : Day.Offset) : Scalar :=
  ⟨scalar.days - days⟩

/--
Converts a `Scalar` to a `Day.Offset`.
-/
def toOffset (scalar : Scalar) : Day.Offset :=
  scalar.days

/--
Creates a `Scalar` from a `Day.Offset`.
-/
def ofOffset (offset : Day.Offset) : Scalar :=
  ⟨offset⟩

end Scalar
end Date
