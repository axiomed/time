import Time.DateTime
import Time.Bounded
import Lean.Data.Parsec

namespace Time

open Time.Date
open Time.Time
open Lean.Parsec

private inductive DateTimeFormat
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
  | str (str: String)
  deriving Repr

abbrev Format := List DateTimeFormat

private def isLetter (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

private def isNonLetter (c: Char) : Bool := ¬isLetter c

private def specParserToken : Lean.Parsec DateTimeFormat
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
  <|> (pchar '\\') *> anyChar <&> (.str ∘ toString)
  <|> (pchar '\"' *>  many1Chars (satisfy (· ≠ '\"')) <* pchar '\"') <&> .str
  <|> (pchar '\'' *>  many1Chars (satisfy (· ≠ '\'')) <* pchar '\'') <&> .str
  <|> many1Chars (satisfy isNonLetter) <&> .str

private def specParser : Lean.Parsec Format :=
  (Array.toList <$> Lean.Parsec.many specParserToken) <* eof

private def specParse (s: String) : Except String Format :=
  specParser.run s

private def Format.spec! (s: String) : Format :=
  match specParser.run s with
  | .ok s => s
  | .error s => panic! s

-- Spec formatter

private def unabbrevMonth (month: Month) : String :=
  match month.val, month.bounds with
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

private def abbrevMonth (month: Month) : String :=
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

private def formatWithDate (date : DateTime tz) : DateTimeFormat → String
  | .YYYY  => s!"{leftPad 4 '0' (toString date.data.date.year)}"
  | .YY    => s!"{leftPad 2 '0' (toString $ date.data.date.year % 100)}"
  | .MMMM  => unabbrevMonth date.data.date.month
  | .MMM   => abbrevMonth date.data.date.month
  | .MM    => s!"{leftPad 2 '0' (toString $ date.data.date.month)}"
  | .M     => s!"{date.data.date.month}"
  | .DD    => s!"{leftPad 2 '0' (toString $ date.data.date.day)}"
  | .D     => s!"{date.data.date.day}"
  | .d     => s!"{leftPad 2 ' ' $ toString date.data.date.day}"
  | .EEEE  => dayOfWeek date.weekday
  | .EEE   => abbrevDayOfWeek date.weekday
  | .hh    => s!"{leftPad 2 '0' (toString date.data.time.hour)}"
  | .h     => s!"{date.data.time.hour}"
  | .HH    => let hour := date.data.time.hour.val % 12; if hour == 0 then "12" else s!"{leftPad 2 '0' $ toString hour}"
  | .H     => let hour := date.data.time.hour.val % 12; if hour == 0 then "12" else s!"{hour}"
  | .AA    => if date.data.time.hour < 12 then "AM" else "PM"
  | .aa    => if date.data.time.hour < 12 then "am" else "pm"
  | .mm    => s!"{leftPad 2 '0' $ toString date.data.time.minute}"
  | .m     => s!"{date.data.time.minute}"
  | .ss    => s!"{leftPad 2 '0' $ toString date.data.time.second}"
  | .s     => s!"{date.data.time.second}"
  | .ZZZZZ => date.offset.toIsoString true
  | .ZZZZ  => date.offset.toIsoString false
  | .ZZZ   => if date.offset.second = 0 then "UTC" else date.offset.toIsoString false
  | .Z     => if date.offset.second = 0 then "Z" else date.offset.toIsoString true
  | .str s => s
  where
    leftPad (n : Nat) (a : Char) (s : String) : String :=
      "".pushn a (n - s.length) ++ s

private def twoDigit : Lean.Parsec Nat := do
  let digit1 ← Lean.Parsec.digit
  let digit2 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}{digit2}"

private def number : Lean.Parsec Nat := do
  String.toNat! <$> Lean.Parsec.many1Chars Lean.Parsec.digit

private def singleDigit : Lean.Parsec Nat := do
  let digit1 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}"

private def fourDigit : Lean.Parsec Nat := do
  let digit1 ← Lean.Parsec.digit
  let digit2 ← Lean.Parsec.digit
  let digit3 ← Lean.Parsec.digit
  let digit4 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}{digit2}{digit3}{digit4}"

@[simp]
private def SingleFormatType : DateTimeFormat → Type
  | .YYYY => Nat
  | .YY => Nat
  | .MMMM => Month
  | .MMM => Month
  | .MM => Month
  | .M => Month
  | .DD => Day
  | .D => Day
  | .d => Day
  | .EEEE => Weekday
  | .EEE => Weekday
  | .hh => Hour
  | .h => Hour
  | .HH => Hour
  | .H => Hour
  | .AA => HourMarker
  | .aa => HourMarker
  | .mm => Minute
  | .m => Minute
  | .ss => Second
  | .s => Second
  | .ZZZZZ => Offset
  | .ZZZZ => Offset
  | .ZZZ => Offset
  | .Z => Offset
  | .str _ => Unit

private def FormatType (result: Type) : Format → Type
  | .cons entry xs => (SingleFormatType entry) → (FormatType result xs)
  | .nil => result

private def transform (n: β → Option α) (p: Lean.Parsec β) : Lean.Parsec α := do
  let res ← p
  match n res with
  | some n => pure n
  | none => fail "cannot parse"

private def parseMonth : Lean.Parsec Month
  :=  (pstring "Jan" *> pure ⟨1, by decide⟩)
  <|> (pstring "Feb" *> pure ⟨2, by decide⟩)
  <|> (pstring "Mar" *> pure ⟨3, by decide⟩)
  <|> (pstring "Apr" *> pure ⟨4, by decide⟩)
  <|> (pstring "May" *> pure ⟨5, by decide⟩)
  <|> (pstring "Jun" *> pure ⟨6, by decide⟩)
  <|> (pstring "Jul" *> pure ⟨7, by decide⟩)
  <|> (pstring "Aug" *> pure ⟨8, by decide⟩)
  <|> (pstring "Sep" *> pure ⟨9, by decide⟩)
  <|> (pstring "Oct" *> pure ⟨10, by decide⟩)
  <|> (pstring "Nov" *> pure ⟨11, by decide⟩)
  <|> (pstring "Dec" *> pure ⟨12, by decide⟩)

private def parseMonthUnabbrev : Lean.Parsec Month
  :=  (pstring "January" *> pure ⟨1, by decide⟩)
  <|> (pstring "February" *> pure ⟨2, by decide⟩)
  <|> (pstring "March" *> pure ⟨3, by decide⟩)
  <|> (pstring "April" *> pure ⟨4, by decide⟩)
  <|> (pstring "May" *> pure ⟨5, by decide⟩)
  <|> (pstring "June" *> pure ⟨6, by decide⟩)
  <|> (pstring "July" *> pure ⟨7, by decide⟩)
  <|> (pstring "August" *> pure ⟨8, by decide⟩)
  <|> (pstring "September" *> pure ⟨9, by decide⟩)
  <|> (pstring "October" *> pure ⟨10, by decide⟩)
  <|> (pstring "November" *> pure ⟨11, by decide⟩)
  <|> (pstring "December" *> pure ⟨12, by decide⟩)

private def parseWeekday : Lean.Parsec Weekday
  :=  (pstring "Mon" *> pure Weekday.mon)
  <|> (pstring "Tue" *> pure Weekday.tue)
  <|> (pstring "Wed" *> pure Weekday.wed)
  <|> (pstring "Thu" *> pure Weekday.thu)
  <|> (pstring "Fri" *> pure Weekday.fri)
  <|> (pstring "Sat" *> pure Weekday.sat)
  <|> (pstring "Sun" *> pure Weekday.sun)

private def parseWeekdayUnnabrev : Lean.Parsec Weekday
  :=  (pstring "Monday" *> pure Weekday.mon)
  <|> (pstring "Tuesday" *> pure Weekday.tue)
  <|> (pstring "Wednesday" *> pure Weekday.wed)
  <|> (pstring "Thursday" *> pure Weekday.thu)
  <|> (pstring "Friday" *> pure Weekday.fri)
  <|> (pstring "Saturday" *> pure Weekday.sat)
  <|> (pstring "Sunday" *> pure Weekday.sun)

private def parserUpperHourMarker : Lean.Parsec HourMarker
  :=  (pstring "AM" *> pure HourMarker.am)
  <|> (pstring "PM" *> pure HourMarker.pm)

private def parserLowerHourMarker : Lean.Parsec HourMarker
  :=  (pstring "am" *> pure HourMarker.am)
  <|> (pstring "pm" *> pure HourMarker.pm)

private def parseYearTwo : Lean.Parsec Nat :=do
  let year ← twoDigit
  return if year < 70 then 2000 + year else 1900 + year

private def timeOffset (colon: Bool) : Lean.Parsec Offset := do
  let sign ← (pstring "-" *> pure (-1)) <|> (pstring "-" *> pure 1)
  let hour ← twoDigit
  if colon then let _ ← pstring ":"
  let minutes ← twoDigit
  pure (Offset.ofSeconds $ (hour * 3600 + minutes * 60) * sign)

private def timeOrUTC (utcString: String) (colon: Bool) : Lean.Parsec Offset :=
  (pstring utcString *> pure Offset.zero) <|> timeOffset colon

private def parserWithFormat : (typ: DateTimeFormat) → Lean.Parsec (SingleFormatType typ)
  | .YYYY => fourDigit
  | .YY => parseYearTwo
  | .MMMM => parseMonthUnabbrev
  | .MMM => parseMonth
  | .MM => transform Nat.Bounded.ofNat? twoDigit
  | .M => transform Nat.Bounded.ofNat? number
  | .DD => transform Nat.Bounded.ofNat? twoDigit
  | .D => transform Nat.Bounded.ofNat? number
  | .d => transform Nat.Bounded.ofNat? (Lean.Parsec.orElse twoDigit (λ_ => pchar ' ' *> (singleDigit)))
  | .EEEE => parseWeekdayUnnabrev
  | .EEE => parseWeekday
  | .hh => transform Fin.ofNat? twoDigit
  | .h => transform Fin.ofNat? number
  | .HH => transform Fin.ofNat? twoDigit
  | .H => transform Fin.ofNat? number
  | .AA => parserUpperHourMarker
  | .aa => parserLowerHourMarker
  | .mm => transform Fin.ofNat? twoDigit
  | .m => transform Fin.ofNat? number
  | .ss => transform Fin.ofNat? twoDigit
  | .s => transform Fin.ofNat? number
  | .ZZZZZ => timeOffset true
  | .ZZZZ => timeOffset false
  | .ZZZ => timeOrUTC "UTC" false
  | .Z => timeOrUTC "Z" true
  | .str s => pstring s *> pure ()

private structure Options where
  marker : Option HourMarker

private def addDataInDateTime (data: Time.DateTime tz) (typ: DateTimeFormat) (value: SingleFormatType typ) : Time.DateTime tz :=
  match typ with
  | .YYYY => DateLike.setYear data value
  | .YY => DateLike.setYear data value
  | .MMMM => DateLike.setMonth data value
  | .MMM => DateLike.setMonth data value
  | .MM => DateLike.setMonth data value
  | .M => DateLike.setMonth data value
  | .DD => DateLike.setDay data value
  | .D => DateLike.setDay data value
  | .d => DateLike.setDay data value
  | .EEEE => data
  | .EEE => data
  | .hh => TimeLike.setHour data value
  | .h => TimeLike.setHour data value
  | .HH => TimeLike.setHour data value
  | .H => TimeLike.setHour data value
  | .AA => TimeLike.setHour data (HourMarker.toAbsolute value (TimeLike.hour data))
  | .aa => TimeLike.setHour data (HourMarker.toAbsolute value (TimeLike.hour data))
  | .mm => TimeLike.setMinute data value
  | .m => TimeLike.setMinute data value
  | .ss => TimeLike.setSecond data value
  | .s => TimeLike.setSecond data value
  | .ZZZZZ => { data with offset := value }
  | .ZZZZ => { data with offset := value }
  | .ZZZ => { data with offset := value }
  | .Z => { data with offset := value }
  | .str _ => data

private def parserFormatD (format: Format) (func: FormatType α format) : Lean.Parsec α :=
  match format with
  | .cons entry xs => do
    let data ← parserWithFormat entry
    let func: _ → _ := by
      rw [FormatType] at func
      exact func
    parserFormatD xs (func data)
  | .nil => pure func

private def parserFormat (format: Format) (func: DateTime tz) : Lean.Parsec (DateTime tz) :=
  match format with
  | .cons entry xs => do
    let data ← parserWithFormat entry
    parserFormat xs (addDataInDateTime func entry data)
  | .nil => pure func

private def parserToDate (format: Format) : Lean.Parsec (DateTime tz) :=
  parserFormat format Inhabited.default

def Format.format (x: Format) (date : DateTime tz) : String :=
  x.map (formatWithDate date)
  |> String.join

def Format.parseCallback (format: Format) (str: String) (callback: FormatType α format) : Except String α :=
  (parserFormatD format callback).run str

def Format.parse (format: Format) (str: String) : Except String (DateTime tz) :=
  (parserToDate format).run str

def Format.convert (from_: Format) (to: Format) (subject: String) : Except String String := do
  let date ← from_.parse (tz := .UTC) subject
  return to.format date

def Formats.RFC3339 := Format.spec! "YYYY-MM-DD'T'hh:mm:ssZZZZZ"

def Formats.ISO8601 := Format.spec! "YYYY-MM-DD'T'hh:mm:ss'Z'"

def Formats.AmericanDate := Format.spec! "MM/DD/YYYY"

def Formats.EuropeanDate := Format.spec! "DD/MM/YYYY"

def Formats.Time12Hour := Format.spec! "HH:mm:ss aa"

def Formats.Time24Hour := Format.spec! "hh:mm:ss"

def Formats.SQLDate := Format.spec! "YYYY-MM-DD"

def Formats.DayMonthYear := Format.spec! "EEEE, MMMM D, YYYY"

def Formats.LongDateFormat := Format.spec! "EEEE, MMMM D, YYYY hh:mm:ss"

def Formats.AscTime := Format.spec! "EEE MMM d hh:mm:ss YYYY"

def Formats.RFC822 := Format.spec! "DD MMM YYYY hh:mm ZZZ"

def Formats.RFC850 := Format.spec! "EEEE, DD-MMM-YY hh:mm:ss ZZZ"
