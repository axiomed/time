/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Basic

namespace Time

structure Scalar where
  seconds : Second.Offset
  nanos : Nanosecond.Ordinal

namespace Scalar

def toSeconds (time : Scalar) : Second.Offset :=
  time.seconds

def toMinutes (time : Scalar) : Minute.Offset :=
  time.seconds.toMinutes

def toHours (time : Scalar) : Hour.Offset :=
  time.seconds.toHours

end Scalar
end Time
