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
`Offset` represents an offset in nanoseconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal (1 / 1000000000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩
