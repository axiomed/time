/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Date
import Time.Time
import Lean.Data.Parsec

namespace Format
open Lean.Parsec Time Date

private inductive Modifier
  | YYYY
  | YY
  | MMMM
  | MMM
  | MM
  | M
  | DD
  | D
  | d
  | EEEE
  | EEE
  | hh
  | h
  | HH
  | H
  | AA
  | aa
  | mm
  | m
  | ss
  | s
  | ZZZZZ
  | ZZZZ
  | ZZZ
  | Z
  deriving Repr

/--
The part of a formatting string. a string is just a text and a modifier is in the format `%0T` where
0 is the quantity of left pad and `T` the `Modifier`.
-/
private inductive FormatPart
  | string (val : String)
  | modifier (left_pad: Nat) (modifier : Modifier)
  deriving Repr

/--
The format of date and time string.
-/
abbrev Format := List FormatPart

private def isLetter (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

private def isNonLetter (c: Char) : Bool := ¬isLetter c

private def parseModifier : Lean.Parsec Modifier
  :=  pstring "YYYY" *> pure .YYYY
  <|> pstring "YY" *> pure .YY
  <|> pstring "MMMM" *> pure .MMMM
  <|> pstring "MMM" *> pure .MMM
  <|> pstring "MM" *> pure .MM
  <|> pstring "M" *> pure .M
  <|> pstring "DD" *> pure .DD
  <|> pstring "D" *> pure .D
  <|> pstring "d" *> pure .d
  <|> pstring "EEEE" *> pure .EEEE
  <|> pstring "EEE" *> pure .EEE
  <|> pstring "hh" *> pure .hh
  <|> pstring "h" *> pure .h
  <|> pstring "HH" *> pure .HH
  <|> pstring "H" *> pure .H
  <|> pstring "AA" *> pure .AA
  <|> pstring "aa" *> pure .aa
  <|> pstring "mm" *> pure .mm
  <|> pstring "m" *> pure .m
  <|> pstring "ss" *> pure .ss
  <|> pstring "s" *> pure .s
  <|> pstring "ZZZZZ" *> pure .ZZZZZ
  <|> pstring "ZZZZ" *> pure .ZZZZ
  <|> pstring "ZZZ" *> pure .ZZZ
  <|> pstring "Z" *> pure .Z

private def pnumber : Lean.Parsec Nat := do
  let numbers ← manyChars digit
  return numbers.foldl (λacc char => acc * 10 + (char.toNat - 48)) 0

private def parseFormatPart : Lean.Parsec FormatPart
  := (.modifier <$> (pchar '%' *> pnumber) <*> parseModifier)
  <|> (pchar '\\') *> anyChar <&> (.string ∘ toString)
  <|> (pchar '\"' *>  many1Chars (satisfy (· ≠ '\"')) <* pchar '\"') <&> .string
  <|> (pchar '\'' *>  many1Chars (satisfy (· ≠ '\'')) <* pchar '\'') <&> .string
  <|> many1Chars (satisfy (fun x => x ≠ '%' ∧ x ≠ '\'' ∧ x ≠ '\"')) <&> .string

private def specParser : Lean.Parsec Format :=
  (Array.toList <$> Lean.Parsec.many parseFormatPart) <* eof

private def specParse (s: String) : Except String Format :=
  specParser.run s

def Format.spec! (s: String) : Format :=
  match specParser.run s with
  | .ok s => s
  | .error s => panic! s

-- Pretty printer

private def unabbrevMonth (month: Month.Ordinal) : String :=
  match month.val, month.property with
  | 1, _ => "January"
  | 2, _ => "February"
  | 3, _ => "March"
  | 4, _ => "April"
  | 5, _ => "May"
  | 6, _ => "June"
  | 7, _ => "July"
  | 8, _ => "August"
  | 9, _ => "September"
  | 10, _ => "October"
  | 11, _ => "November"
  | 12, _ => "December"

private def abbrevMonth (month: Month.Ordinal) : String :=
  match month.val, month.property with
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

private def abbrevDayOfWeek (day: Weekday) : String :=
  match day with
  | .sun => "Sun"
  | .mon => "Mon"
  | .tue => "Tue"
  | .wed => "Wed"
  | .thu => "Thu"
  | .fri => "Fri"
  | .sat => "Sat"

private def dayOfWeek (day: Weekday) : String :=
  match day with
  | .sun => "Sunday"
  | .mon => "Monday"
  | .tue => "Tuesday"
  | .wed => "Wednesday"
  | .thu => "Thusday"
  | .fri => "Friday"
  | .sat => "Saturday"

private def formatWithDate (date : ZonedDateTime) : Modifier → String
  | .YYYY  => s!"{leftPad 4 '0' (toString date.data.date.year)}"
  | .YY    => s!"{leftPad 2 '0' (toString $ date.data.date.year.toNat % 100)}"
  | .MMMM  => unabbrevMonth date.data.date.month
  | .MMM   => abbrevMonth date.data.date.month
  | .MM    => s!"{leftPad 2 '0' (toString $ date.data.date.month.toNat)}"
  | .M     => s!"{date.data.date.month.toNat}"
  | .DD    => s!"{leftPad 2 '0' (toString $ date.data.date.day.toNat)}"
  | .D     => s!"{date.data.date.day.toNat}"
  | .d     => s!"{leftPad 2 ' ' $ toString date.data.date.day.toNat}"
  | .EEEE  => dayOfWeek date.weekday
  | .EEE   => abbrevDayOfWeek date.weekday
  | .hh    => s!"{leftPad 2 '0' (toString date.data.time.hour.toNat)}"
  | .h     => s!"{date.data.time.hour.toNat}"
  | .HH    => let hour := date.data.time.hour.val % 12; if hour == 0 then "12" else s!"{leftPad 2 '0' $ toString hour}"
  | .H     => let hour := date.data.time.hour.val % 12; if hour == 0 then "12" else s!"{hour}"
  | .AA    => if date.data.time.hour.toNat < 12 then "AM" else "PM"
  | .aa    => if date.data.time.hour.toNat < 12 then "am" else "pm"
  | .mm    => s!"{leftPad 2 '0' $ toString date.data.time.minute.toNat}"
  | .m     => s!"{date.data.time.minute.toNat}"
  | .ss    => s!"{leftPad 2 '0' $ toString date.data.time.second.toNat}"
  | .s     => s!"{date.data.time.second.toNat}"
  | .ZZZZZ => date.offset.toIsoString true
  | .ZZZZ  => date.offset.toIsoString false
  | .ZZZ   => if date.offset.second = 0 then "UTC" else date.offset.toIsoString false
  | .Z     => if date.offset.second = 0 then "Z" else date.offset.toIsoString true
  | .str s => s
  where
    leftPad (n : Nat) (a : Char) (s : String) : String :=
      "".pushn a (n - s.length) ++ s

-- Parser
