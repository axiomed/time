/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data.Int
import Time.Classes
import Time.Time

namespace DateTime
open Time

/--
Seconds since the UNIX Epoch.
-/
def Timestamp := Second.Offset
  deriving Repr, BEq

instance : OfNat Timestamp n where
  ofNat := UnitVal.ofNat n
