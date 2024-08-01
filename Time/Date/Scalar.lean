/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Date.Basic

namespace Date

structure Scalar where
  days : Day.Offset

instance : Add Scalar where
  add x y := ⟨x.days + y.days⟩
