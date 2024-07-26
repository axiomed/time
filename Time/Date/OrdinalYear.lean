import Time.Date.Basic
import LeanCopilot

namespace Time.Date

/-- Represents a date with a year and an ordinal day (day of the year). -/
structure YO where
  year : Year
  ordinal : Ordinal year.isLeap
  deriving Repr

instance : DateLike YO where
  year date := date.year
  month date := (Month.ofOrdinal date.year.isLeap date.ordinal).fst
  day date := (Month.ofOrdinal date.year.isLeap date.ordinal).snd

def YO.civilFromDate (date: YO) : Int :=
  let (m, d) := Month.ofOrdinal date.year.isLeap date.ordinal
  let y : Int := if m.val > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := m.val
  let d : Int := d.val
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  (era * 146097 + doe - 719468)
