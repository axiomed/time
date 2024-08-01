/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Bounded
import Time.Time

open Time

/--
Time duration with nanosecond precision. This type allows negative duration.
-/
structure Duration where
  seconds : Second.Offset
  nanos : Nanosecond.Offset

namespace Duration
