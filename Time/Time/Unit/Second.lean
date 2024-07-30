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

namespace Time
open Lean

namespace Second

/--
The `unit` definition expresses the quantity of seconds that a `Second` represents.
In this case, it is set to 1.
-/
def unit : Rat := 1

/--
`Ordinal` represents a bounded value for seconds, which ranges between 0 and 61.
This accounts for potential leap seconds.
-/
def Ordinal := Bounded.LE 0 60
  deriving Repr, BEq, LE

instance [Le n 60] : OfNat Ordinal n where ofNat := Bounded.LE.ofNat n Le.p

instance : Inhabited Ordinal where default := 0

/--
`Offset` represents an offset in seconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 1
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
def ofNat (data : Nat) (h: data ≤ 60 := by decide) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
def ofFin (data : Fin 61) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`.
-/
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal

namespace Offset

/--
Converts an `Offset` to another unit type.
-/
def convert (val : UnitVal a) : UnitVal b :=
  let ratio := b.div a
  UnitVal.ofInt <| val.toInt * ratio.num / ratio.den

end Offset
end Second
