/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Basic

namespace Time

structure Time where
  hours : Hour.Ordinal
  minutes : Minute.Ordinal
  seconds : Second.Ordinal
  deriving Repr, Inhabited

def Time.toSeconds (time : Time) : Second.Offset :=
  time.hours.toOffset.toSeconds +
  time.minutes.toOffset.toSeconds +
  time.seconds.toOffset

def Time.toMinutes (time : Time) : Minute.Offset :=
  time.hours.toOffset.toMinutes +
  time.minutes.toOffset +
  time.seconds.toOffset.toMinutes
