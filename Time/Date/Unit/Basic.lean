/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Date.Unit.Day
import Time.Date.Unit.Month
import Time.Date.Unit.Year
import Time.Date.Unit.Weekday
import Time.Date.Unit.WeekOfYear

namespace Std
namespace Time.Day.Ordinal.OfYear

set_option linter.all true

/--
Conevrts a `Year` and a `Ordinal.OfYear` to a valid day and month.
-/
@[inline]
def toMonthAndDay (year : Year.Offset) (ordinal : OfYear year.isLeap) : { val : Month.Ordinal × Day.Ordinal // Year.Offset.Valid year (Prod.fst val) (Prod.snd val) } :=
  Month.Ordinal.ofOrdinal ordinal

end Time.Day.Ordinal.OfYear
end Std
