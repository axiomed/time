import Time.Date

namespace Time.Format.RF2822

/-- Helper function to convert a day of the week to its RFC 2822 abbreviation. -/
def dayOfWeek (day: Weekday) : String :=
  match day with
  | .sun => "Sun"
  | .mon => "Mon"
  | .tue => "Tue"
  | .wed => "Wed"
  | .thu => "Thu"
  | .fri => "Fri"
  | .sat => "Sat"

/-- Helper function to convert a month to its RFC 2822 abbreviation. -/
def month (month: Month) : String :=
  match month.val, month.bounds with
  | 1, _ => "Jan"
  | 2, _ => "Feb"
  | 3, _ => "Mar"
  | 4, _ => "Apr"
  | 5, _ => "May"
  | 6, _ => "Jun"
  | 7, _ => "Jul"
  | 8, _ => "Aug"
  | 9, _ => "Sep"
  | 10, _ => "Oct"
  | 11, _ => "Nov"
  | 12, _ => "Dec"

/-- Parses a string representing a weekday abbreviation (e.g., "Sun", "Mon", etc.) into the
corresponding `Weekday` enum. -/
def parseWeekday (str : String) : Option Weekday :=
  match str.trim with
  | "Sun" => some Weekday.sun
  | "Mon" => some Weekday.mon
  | "Tue" => some Weekday.tue
  | "Wed" => some Weekday.wed
  | "Thu" => some Weekday.thu
  | "Fri" => some Weekday.fri
  | "Sat" => some Weekday.sat
  | _ => none

/-- Parses a string representing a month abbreviation (e.g., "Jan", "Feb", etc.) into the
corresponding `Month` enum. -/
def parseMonth (str : String) : Option Month :=
  match str.trim with
  | "Jan" => some ⟨1, by decide⟩
  | "Feb" => some ⟨2, by decide⟩
  | "Mar" => some ⟨3, by decide⟩
  | "Apr" => some ⟨4, by decide⟩
  | "May" => some ⟨5, by decide⟩
  | "Jun" => some ⟨6, by decide⟩
  | "Jul" => some ⟨7, by decide⟩
  | "Aug" => some ⟨8, by decide⟩
  | "Sep" => some ⟨9, by decide⟩
  | "Oct" => some ⟨10, by decide⟩
  | "Nov" => some ⟨11, by decide⟩
  | "Dec" => some ⟨12, by decide⟩
  | _ => none
