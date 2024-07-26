import Time.Date.Basic

namespace Time.Date

/-- Represents a date with a year and an ordinal day (day of the year). -/
structure OrdinalYear where
  year : Year
  ordinal : Ordinal year.isLeap
  deriving Repr
