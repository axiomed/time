import Time.IO

namespace Time.Local

structure Offset where
  hour: Int
  second: Int
  deriving Repr, Inhabited

def Offset.toIsoString (offset : Offset) (colon: Bool) : String :=
  let (sign, time) := if offset.second >= 0 then ("+", offset.second) else ("-", -offset.second)
  let hour := Int.div time 3600
  let minutes := Int.div (Int.mod time 3600) 60
  let hourStr := if hour < 10 then s!"0{hour}" else toString hour
  let minuteStr := if minutes < 10 then s!"0{minutes}" else toString minutes
    if colon then s!"{sign}{hourStr}:{minuteStr}"
    else s!"{sign}{hourStr}{minuteStr}"

def Offset.zero : Offset := { hour := 0, second := 0 }

def Offset.ofHours (n: Int) : Offset := Offset.mk n (n*3600)

def Offset.ofSeconds (n: Int) : Offset := Offset.mk (n/3600) n

/-- An enumeration representing different time zones. -/
inductive TimeZone
  | GMT
  | UTC
  | offset (val: Offset)
  | local
  deriving Repr

/-- Get the time zone offset in second. -/
def TimeZone.offsetInSeconds : IO Int :=
  Time.primTimeOffset

/-- Get the time zone offset in hour. -/
def TimeZone.offsetInHours : IO Int :=
  (· / 3600) <$> TimeZone.offsetInSeconds

/-- Get the local time zone. -/
def TimeZone.getLocalOffset : IO Offset := do
  let second ← TimeZone.offsetInSeconds
  let hour := second / 3600
  return Offset.mk hour second

/-- Gets the local offset by the timezone -/
def TimeZone.toOffset : TimeZone → IO Offset
  | .GMT => pure (Offset.mk 0 0)
  | .UTC => pure (Offset.mk 0 0)
  | .offset val => pure val
  | .local => getLocalOffset
