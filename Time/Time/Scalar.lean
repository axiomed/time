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

def Scalar.toSeconds (time : Scalar) : Second.Offset :=
  time.seconds

def Scalar.toMinutes (time : Scalar) : Minute.Offset :=
  time.seconds.toMinutes

def Scalar.toHours (time : Scalar) : Hour.Offset :=
  time.seconds.toHours
