/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.UnitVal
import Time.Bounded
import Time.LessEq
import Lean.Data.Rat
import Time.Time.Unit.Millisecond

namespace Std
namespace Time

set_option linter.all true

namespace Nanosecond

/--
`Ordinal` represents a bounded value for second, which ranges between 0 and 60.
This accounts for potential leap second.
-/
def Ordinal := Bounded.LE 0 999999999
  deriving Repr, BEq, LE, LT

instance : OfNat Ordinal n where ofNat := Bounded.LE.ofFin (Fin.ofNat n)

instance : Inhabited Ordinal where default := 0

namespace Ordinal

/--
Convert to `Millisecond.Ordinal`
-/
def toMillisecond (nano : Ordinal) : Millisecond.Ordinal :=
  nano.div 1000000 (by decide)

/--
Convert from `Millisecond.Ordinal`
-/
def ofMillisecond (nano : Millisecond.Ordinal) : Nanosecond.Ordinal :=
  nano.mul_pos 1000000 (by decide)
  |>.expandTop (by decide)

end Ordinal

/--
`Offset` represents an offset in nanoseconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal (1 / 1000000000)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

/--
`Span` represents a bounded value for nanoseconds, ranging between -999999999 and 999999999.
This can be used for operations that involve differences or adjustments within this range.
-/
def Span := Bounded.LE (-999999999) 999999999
  deriving Repr, BEq, LE, LT

instance : Inhabited Span where default := Bounded.LE.mk 0 (by decide)
