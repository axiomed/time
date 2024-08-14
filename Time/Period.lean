/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Zoned

namespace Std
namespace Time
open Internal

/--
A period of time that is used to artithmetic stuff.
-/
structure Period where
  year: Year.Offset
  month: Month.Offset
  day: Day.Offset
