/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Internal
import Init.Data.Int
import Time.Time

namespace Std
namespace Time
open Internal

/--
Seconds since the UNIX Epoch.
-/
def Timestamp := Second.Offset
  deriving Repr, BEq, Inhabited

namespace Timestamp

/--
Get the current monotonic time.
-/
@[extern "lean_get_current_timestamp"]
protected opaque now : IO Timestamp

/--
A function to transform `Timestamp` to `Second.Offset`
-/
@[inline]
def toSeconds (tm : Timestamp) : Second.Offset :=
  tm

instance : OfNat Timestamp n where
  ofNat := UnitVal.ofNat n

instance : HAdd Timestamp Second.Offset Timestamp where
  hAdd x y := UnitVal.add x y

instance : HSub Timestamp Second.Offset Timestamp where
  hSub x y := UnitVal.sub x y

end Timestamp
end Time
end Std
