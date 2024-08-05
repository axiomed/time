/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Time.Format.Basic

open Std.Time

namespace Formats

set_option linter.all true

/--
The ISO8601 format, which is always 24 or 27 characters long, used for representing date and time in
a standardized format. The format follows the pattern `YYYY-MM-DD'T'hh:mm:ss'Z'`.
-/
def ISO8601 : Format .any := Format.spec! "YYYY-MM-DD'T'hh:mm:ss.sssZ"

/--
The AmericanDate format, which follows the pattern `MM/DD/YYYY`.
-/
def AmericanDate : Format .any := ⟨[Modifier.MM, "/", Modifier.DD, "/", Modifier.YYYY]⟩

/--
The EuropeanDate format, which follows the pattern `DD/MM/YYYY`.
-/
def EuropeanDate : Format .any := ⟨[Modifier.DD, "/", Modifier.MM, "/", Modifier.YYYY]⟩

/--
The Time12Hour format, which follows the pattern `hh:mm:ss aa` for representing time
in a 12-hour clock format with an AM/PM marker.
-/
def Time12Hour : Format .any := ⟨[Modifier.HH, ":", Modifier.mm, ":", Modifier.ss, " ", Modifier.aa]⟩

/--
The Time24Hour format, which follows the pattern `hh:mm:ss` for representing time
in a 24-hour clock format.
-/
def Time24Hour : Format .any := ⟨[Modifier.hh, ":", Modifier.mm, ":", Modifier.ss]⟩

/--
The SQLDate format, which follows the pattern `YYYY-MM-DD` and is commonly used
in SQL databases to represent dates.
-/
def SQLDate : Format .any := ⟨[Modifier.YYYY, "-", Modifier.MM, "-", Modifier.DD]⟩

/--
The LongDateFormat, which follows the pattern `EEEE, MMMM D, YYYY hh:mm:ss` for
representing a full date and time with the day of the week and month name.
-/
def LongDateFormat : Format (.only .GMT) := Format.spec! "EEEE, MMMM D, YYYY hh:mm:ss"

/--
The AscTime format, which follows the pattern `EEE MMM d hh:mm:ss YYYY`. This format
is often used in older systems for logging and time-stamping events.
-/
def AscTime : Format (.only .GMT) := Format.spec! "EEE MMM d hh:mm:ss YYYY"

/--
The RFC822 format, which follows the pattern `EEE, DD MMM YYYY hh:mm:ss ZZZ`.
This format is used in email headers and HTTP headers.
-/
def RFC822 : Format .any := Format.spec! "EEE, DD MMM YYYY hh:mm:ss ZZZ"

/--
The RFC850 format, which follows the pattern `EEEE, DD-MMM-YY hh:mm:ss ZZZ`.
This format is an older standard for representing date and time in headers.
-/
def RFC850 : Format .any := Format.spec! "EEEE, DD-MMM-YY hh:mm:ss ZZZ"

end Formats

namespace Date

/--
Parses a date string in the American format (`MM/DD/YYYY`) and returns a `Date`.
-/
def fromAmericanDateString (input : String) : Except String Date := do
  let res ← Formats.AmericanDate.parseBuilder (λm d y => Date.ofYearMonthDay y m d) input
  match res with
  | .some res => pure res
  | none => .error "Invalid date."

end Date

namespace Time

/--
Parses a time string in the 24-hour format (`hh:mm:ss`) and returns a `Time`.
-/
def fromTime24Hour (input : String) : Except String Time :=
  Formats.Time24Hour.parseBuilder (Time.ofHourMinuteSeconds) input

/--
Formats a `Time` value into a 24-hour format string (`hh:mm:ss`).
-/
def toTime24Hour (input : Time) : String :=
  Formats.Time24Hour.formatBuilder input.hour input.minute input.second

/--
Parses a time string in the 12-hour format (`hh:mm:ss aa`) and returns a `Time`.
-/
def fromTime12Hour (input : String) : Except String Time :=
  Formats.Time12Hour.parseBuilder (λh m s a => Time.ofHourMinuteSeconds (HourMarker.toAbsolute! a h) m s) input

/--
Formats a `Time` value into a 12-hour format string (`hh:mm:ss aa`).
-/
def toTime12Hour (input : Time) : String :=
  Formats.Time12Hour.formatBuilder input.hour input.minute input.second (if input.hour.val ≥ 12 then HourMarker.pm else HourMarker.am)

end Time

namespace ZonedDateTime

/--
Parses a `String` in the `ISO8601` format and returns a `DateTime`.
-/
def fromISO8601String (input : String) : Except String ZonedDateTime :=
  Formats.ISO8601.parse input

/--
Formats a `ZonedDateTime` value into an ISO8601 string.
-/
def toISO8601String (date : ZonedDateTime) : String :=
  Formats.ISO8601.format date.snd

/--
Parses a `String` in the `RFC822` format and returns a `DateTime`.
-/
def fromRFC822String (input : String) : Except String ZonedDateTime :=
  Formats.RFC822.parse input

/--
Formats a `ZonedDateTime` value into an RFC822 format string.
-/
def toRFC822String (date : ZonedDateTime) : String :=
  Formats.RFC822.format date.snd

/--
Parses a `String` in the `RFC850` format and returns a `DateTime`.
-/
def fromRFC850String (input : String) : Except String ZonedDateTime :=
  Formats.RFC850.parse input

/--
Formats a `ZonedDateTime` value into an RFC850 format string.
-/
def toRFC850String (date : ZonedDateTime) : String :=
  Formats.RFC850.format date.snd

end ZonedDateTime

namespace DateTime

/--
Parses a `String` in the `AscTime` format and returns a `DateTime` object in the GMT time zone.
-/
def fromAscTimeString (input : String) : Except String (DateTime .GMT) :=
  Formats.AscTime.parse input

/--
Formats a `DateTime` value into an AscTime format string.
-/
def toAscTimeString (datetime : DateTime .GMT) : String :=
  Formats.AscTime.format datetime

/--
Parses a `String` in the `LongDateFormat` and returns a `DateTime` object in the GMT time zone.
-/
def fromLongDateFormatString (input : String) : Except String (DateTime .GMT) :=
  Formats.LongDateFormat.parse input

/--
Formats a `DateTime` value into a LongDateFormat string.
-/
def toLongDateFormatString (datetime : DateTime .GMT) : String :=
  Formats.LongDateFormat.format datetime

/--
Formats a `ZonedDateTime` value into an ISO8601 string.
-/
def toISO8601String (date : ZonedDateTime) : String :=
  Formats.ISO8601.format date.snd

/--
Formats a `ZonedDateTime` value into an RFC822 format string.
-/
def toRFC822String (date : ZonedDateTime) : String :=
  Formats.RFC822.format date.snd

/--
Formats a `ZonedDateTime` value into an RFC850 format string.
-/
def toRFC850String (date : ZonedDateTime) : String :=
  Formats.RFC850.format date.snd

end DateTime
