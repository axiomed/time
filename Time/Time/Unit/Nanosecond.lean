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

set_option linter.all true

namespace Nanosecond

/--
`Ordinal` represents a bounded value for seconds, which ranges between 0 and 60.
This accounts for potential leap seconds.
-/
def Ordinal := Bounded.LE 0 999999999
  deriving Repr, BEq, LE

instance : OfNat Ordinal n where ofNat := Bounded.LE.ofFin (Fin.ofNat n)

instance : Inhabited Ordinal where default := 0

/--
`Offset` represents an offset in nanoseconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal (1 / 1000000000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩
