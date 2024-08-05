/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data.Int
import Time.LessEq
import Time.Time

namespace Std
namespace Time

/--
Seconds since the UNIX Epoch.
-/
def Timestamp := Second.Offset
  deriving Repr, BEq, Inhabited

instance : OfNat Timestamp n where
  ofNat := UnitVal.ofNat n

instance : HAdd Timestamp Second.Offset Timestamp where
  hAdd x y := UnitVal.add x y

instance : HSub Timestamp Second.Offset Timestamp where
  hSub x y := UnitVal.sub x y