import Time.Format.Formatter
import Time.DateTime
import Time.Bounded
import Lean.Data.Parsec

namespace Time.Format.RF2822

open Time.Date
open Lean.Parsec

def format : Formatter.Format := Formatter.Format.spec! "DD MMM YYYY hh:mm ZZZ"

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

/-- Convert a DateTime with a time zone to an RFC 2822 date and time string. -/
def DateTime.toRFC8222 (dt: DateTime tz) : String :=
  let offset := dt.offset.second
  let dayOfWeek := Format.RF2822.dayOfWeek (Date.weekday dt.data.date)
  let day := toString dt.data.date.day
  let month := Format.RF2822.month dt.data.date.month
  let year := toString dt.data.date.year
  let hour := leftPad 2 '0' $ toString dt.data.time.hour
  let minute := leftPad 2 '0' $ toString dt.data.time.minute
  let second := leftPad 2 '0' $ toString dt.data.time.second
  let (sign, offset) := if offset >= 0 then ("+", offset) else ("-", -offset)
  let offsetHours := leftPad 2 '0' $ toString (offset / 3600)
  let offsetMinutes := leftPad 2 '0' $ toString ((offset % 3600) / 60)
  s!"{dayOfWeek}, {day} {month} {year} {hour}:{minute}:{second} {sign}{offsetHours}{offsetMinutes}"
where
  leftPad (n : Nat) (a : Char) (s : String) : String :=
    "".pushn a (n - s.length) ++ s

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


def transform (n: β → Option α) (p: Lean.Parsec β) : Lean.Parsec α := do
  let res ← p
  match n res with
  | some n => pure n
  | none => fail "cannot parse"

def parseTime : Lean.Parsec Time := do
  let hour ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ':')
  let minute ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ':')
  let second ← transform Fin.ofNat? (Formatter.twoDigit <* pchar ' ')
  return { hour, minute, second }

def parseDate : Lean.Parsec Date := do
  let day ← transform Nat.Bounded.ofNat? (Formatter.twoDigit <* pchar ' ')
  let month ← ws *> transform parseMonth (many1Chars (satisfy (· ≠ ' ')))
  let year ← ws *> Formatter.fourDigit <* ws
  return { year, month, day }

def parser : Lean.Parsec (DateTime .GMT) := do
  let _ ← transform parseWeekday (many1Chars (satisfy (· ≠ ',')))
  let _ ← pchar ',' <* ws
  let date ← parseDate
  let time ← parseTime
  let _ ← pstring "GMT" *> eof
  return { data := { date, time }, offset := Offset.zero }

def parse (s: String) : Except String (DateTime .GMT) :=
  parser.run s
