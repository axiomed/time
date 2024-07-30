/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.UnitVal
import Time.Time.Unit.Hour
import Time.Time.Unit.Minute
import Time.Time.Unit.Second

namespace Time

namespace Second.Offset

@[inline, specialize]
def toMinutes (offset : Second.Offset) : Minute.Offset :=
  offset.div 60

@[inline]
def toHours (offset : Second.Offset) : Hour.Offset :=
  offset.div 3600

end Second.Offset

namespace Minute.Offset

@[inline]
def toHours (offset : Minute.Offset) : Hour.Offset :=
  offset.div 60

end Minute.Offset

end Time
