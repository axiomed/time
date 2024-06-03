import Time.Format.Formatter
import Time.DateTime
import Time.Bounded
import Lean.Data.Parsec

namespace Time.Format.RFC860

open Time.Date
open Lean.Parsec

/-- Helper function to convert a day of the week to its RFC 860 full name. -/
def dayOfWeekFull (day: Weekday) : String :=
  match day with
  | .sun => "Sunday"
  | .mon => "Monday"
  | .tue => "Tuesday"
  | .wed => "Wednesday"
  | .thu => "Thursday"
  | .fri => "Friday"
  | .sat => "Saturday"

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

/-- Convert a DateTime with a time zone to an RFC 860 date and time string. -/
def DateTime.toRFC860 (dt: DateTime tz) : String :=
  let dayOfWeek := Format.RFC860.dayOfWeekFull (Date.weekday dt.data.date)
  let day := leftPad 2 '0' $ toString dt.data.date.day
  let month := month dt.data.date.month
  let year := leftPad 2 '0' $ toString (dt.data.date.year % 100)
  let hour := leftPad 2 '0' $ toString dt.data.time.hour
  let minute := leftPad 2 '0' $ toString dt.data.time.minute
  let second := leftPad 2 '0' $ toString dt.data.time.second
  s!"{dayOfWeek}, {day}-{month}-{year} {hour}:{minute}:{second} GMT"
where
  leftPad (n : Nat) (a : Char) (s : String) : String :=
    "".pushn a (n - s.length) ++ s

/-- Parses a string representing a full weekday name into the corresponding `Weekday` enum. -/
def parseWeekdayFull (str : String) : Option Weekday :=
  match str.trim with
  | "Sunday" => some Weekday.sun
  | "Monday" => some Weekday.mon
  | "Tuesday" => some Weekday.tue
  | "Wednesday" => some Weekday.wed
  | "Thursday" => some Weekday.thu
  | "Friday" => some Weekday.fri
  | "Saturday" => some Weekday.sat
  | _ => none

def transform (n: β → Option α) (p: Lean.Parsec β) : Lean.Parsec α := do
  let res ← p
  match n res with
  | some n => pure n
  | none => fail "cannot parse"

def garantee (data: Option β) : Lean.Parsec β :=
  match data with
  | some n => pure n
  | none => fail "cannot parse"

def parseTime : Lean.Parsec Time := do
  let hour ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ':')
  let minute ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ':')
  let second ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ' ')
  return { hour, minute, second }

def parseDate : Lean.Parsec Date := do
  let day ← transform Nat.Bounded.ofNat? (Formatter.twoDigit <* pchar '-')
  let month ← ws *> transform parseMonth (many1Chars (satisfy (· ≠ '-'))) <* pchar '-'
  let year ← Formatter.twoDigit <* ws
  let year := if year < 70 then 2000 + year else 1900 + year
  return { year, month, day }

def parser : Lean.Parsec (DateTime .GMT) := do
  let _ ← transform parseWeekdayFull (many1Chars (satisfy (· ≠ ',')))
  let _ ← pchar ',' <* ws
  let date ← parseDate
  let time ← parseTime
  let _ ← pstring "GMT" *> eof
  return { data := { date, time }, offset := Offset.zero }

def parse (s: String) : Except String (DateTime .GMT) :=
  parser.run s
