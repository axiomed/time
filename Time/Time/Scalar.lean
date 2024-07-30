/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Time.Basic

namespace Time

structure ScalarTime where
  seconds : Second.Offset

def ScalarTime.toSeconds (time : ScalarTime) : Second.Offset :=
  time.seconds

def ScalarTime.toMinutes (time : ScalarTime) : Minute.Offset :=
  time.seconds.toMinutes

def ScalarTime.toHours (time : ScalarTime) : Hour.Offset :=
  time.seconds.toHours
