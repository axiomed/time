import Time.Format.Formatter
import Time.DateTime
import Time.Bounded
import Lean.Data.Parsec

namespace Time.Format.AscTime

open Time.Date
open Lean.Parsec

/-- Convert a DateTime with a time zone to an `AscTime` date and time string. -/
def DateTime.toAscTime (dt: DateTime tz) : String :=
  let dayOfWeek := Formatter.abbrevDayOfWeek (Date.weekday dt.data.date)
  let month := Formatter.abbrevMonth dt.data.date.month
  let day := toString dt.data.date.day
  let hour := leftPad 2 '0' $ toString dt.data.time.hour
  let minute := leftPad 2 '0' $ toString dt.data.time.minute
  let second := leftPad 2 '0' $ toString dt.data.time.second
  let year := toString dt.data.date.year
  s!"{dayOfWeek} {month} {day} {hour}:{minute}:{second} {year}"
where
  leftPad (n : Nat) (a : Char) (s : String) : String :=
    "".pushn a (n - s.length) ++ s

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

def parser : Lean.Parsec (DateTime .GMT) := do
  let _ ← Formatter.parseWeekday
  let month ← ws *> Formatter.parseMonth
  let day ← pchar ' ' *> transform Nat.Bounded.ofNat? (Lean.Parsec.orElse Formatter.twoDigit (λ_ => pchar ' ' *> (singleDigit)))
  let time ← ws *> parseTime
  let year ← ws *> Formatter.fourDigit <* ws
  let _ ← eof
  return { data := { date :=  { year, month, day }, time }, offset := Offset.zero }

def parse (s: String) : Except String (DateTime .GMT) :=
  parser.run s
