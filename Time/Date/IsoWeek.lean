import Time.Date.Basic

namespace Time.Date

/-- Represents a date using year, month and day. -/
structure WeekDate where
  year: Year
  week: WeekOfYear
  weekday: Weekday
  deriving Repr
