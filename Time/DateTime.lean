import Time.Epoch
import Time.Date
import Time.Time
import Time.IO

namespace Time

/-! Time manipulation utilities for Date and Time together. -/

open Time.Constants

/--Naive representation of date and time without considering UTC offsets. -/
structure NaiveDateTime where
  date: Date
  time: Time
  deriving Repr, Inhabited

instance : DateLike NaiveDateTime where
  year := Date.year ∘ NaiveDateTime.date
  month := Date.month ∘ NaiveDateTime.date
  day := Date.day ∘ NaiveDateTime.date

  setYear date value := { date with date := DateLike.setYear date.date value }
  setMonth date value := { date with date := DateLike.setMonth date.date value }
  setDay date value := { date with date := DateLike.setDay date.date value }

instance : TimeLike NaiveDateTime where
  hour := Time.hour ∘ NaiveDateTime.time
  minute := Time.minute ∘ NaiveDateTime.time
  second := Time.second ∘ NaiveDateTime.time

  setHour date value := { date with time := TimeLike.setHour date.time value }
  setMinute date value := { date with time := TimeLike.setMinute date.time value }
  setSecond date value := { date with time := TimeLike.setSecond date.time value }

/-- Converts a NaiveDateTime to an Epoch. -/
def NaiveDateTime.toEpoch (dt: NaiveDateTime) : Epoch :=
  let days := (Date.civilFromDate dt.date).toNat
  let second := dt.time.toSecs
  Fin.byMod (days * 86400 + second) 253402300800

/-- Converts an Epoch to a NaiveDateTime by calculating the corresponding date and time. -/
def NaiveDateTime.ofEpoch (epoch: Epoch) : NaiveDateTime := Id.run $ do
  let daySecs : Fin 86400 := Fin.byMod epoch 86400

  let second := Fin.byMod daySecs 60
  let minute := Fin.divMax (Fin.byMod daySecs 3600) 60
  let hour := Fin.divMax daySecs 3600

  let daysSinceEpoch := Fin.divMax epoch 86400
  let boundedDaysSinceEpoch := Int.Bounded.ofFin daysSinceEpoch

  let days := Int.Bounded.sub boundedDaysSinceEpoch leapYearEpoch

  let mut quadracentennialCycles := days.data / daysPer400Y;
  let mut remDays := days.data % daysPer400Y;

  if remDays < 0 then
    remDays := remDays + daysPer400Y
    quadracentennialCycles := quadracentennialCycles - 1

  let mut centenialCycles := remDays / daysPer100Y;

  if centenialCycles = 4 then
    centenialCycles := centenialCycles - 1

  remDays := remDays - centenialCycles * daysPer100Y
  let mut quadrennialCycles := remDays / daysPer4Y;

  if quadrennialCycles = 25 then
    quadrennialCycles := quadrennialCycles - 1

  remDays := remDays - quadrennialCycles * daysPer4Y
  let mut remYears := remDays / 365;

  if remYears = 4 then
    remYears := remYears - 1

  remDays := remDays - remYears * 365
  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles
  let months := [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
  let mut mon : Fin 13 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat (Int.toNat remDays)

  let hmon ←
    if h₁ : mon.val > 10 then
      year := year + 1
      let h := Nat.sub_le_sub_right h₁ 10
      let h₂ := Nat.lt_trans (Nat.sub_lt_self (by decide) (Nat.le_of_lt h₁)) mon.isLt
      pure $ Month.mk (mon.val - 10) (And.intro h h₂)
    else
      let lt := Nat.le_of_not_gt h₁
      let lt := Nat.add_lt_add_right (Nat.lt_succ_iff.mpr lt) 2
      pure $ Month.mk (mon.val + 2) (And.intro (Nat.lt_succ_iff.mpr $ Nat.zero_le (mon + 1)) lt)

  return {
    date := { year := Int.toNat year, month := hmon, day := Day.ofFin mday },
    time := { second, minute, hour }
  }

/-- Subtract a given number of second from a NaiveDateTime. -/
def NaiveDateTime.subSecs (dt: NaiveDateTime) (secondsToSubtract: Nat) : NaiveDateTime :=
  let daysToSubtract := secondsToSubtract / 86400
  let dayToSubtract := secondsToSubtract % 86400
  let date := dt.date.subDays daysToSubtract
  if dayToSubtract > dt.time.toSecs
    then ⟨date.subDays 1, Time.ofSecs (86400 - dayToSubtract)⟩
    else ⟨date, dt.time.subSecs dayToSubtract⟩

/-- Add a given number of second to a NaiveDateTime. -/
def NaiveDateTime.addSecs (dt: NaiveDateTime) (secondsToAdd: Int) : NaiveDateTime :=
  let daysToAdd := Int.div secondsToAdd 86400
  let dayToAdd := Int.mod secondsToAdd 86400
  let date := dt.date.addDays daysToAdd
  if dt.time.toSecs + dayToAdd ≥ 86400 then
    ⟨date.addDays 1, Time.ofSecs ((dt.time.toSecs + dayToAdd) - 86400).toNat⟩
  else if dt.time.toSecs + dayToAdd < 0 then
    dbg_trace dayToAdd
    ⟨date.subDays 1, Time.ofSecs (86400 + (dt.time.toSecs + dayToAdd)).toNat⟩
  else
    dbg_trace dayToAdd
    ⟨date, dt.time.addSecs dayToAdd⟩

/-- Get the current NaiveDateTime based on the current Epoch time. -/
def NaiveDateTime.now : IO NaiveDateTime := do
  let epoch ← Epoch.now
  return NaiveDateTime.ofEpoch epoch

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

/-- Structure representing a DateTime with a time zone. -/
structure DateTime (tz: TimeZone) where
  data: NaiveDateTime
  offset: Offset
  deriving Repr, Inhabited

instance : DateLike (DateTime tz) where
  year := DateLike.year ∘ DateTime.data
  month := DateLike.month ∘ DateTime.data
  day := DateLike.day ∘ DateTime.data

  setYear date value := { date with data := DateLike.setYear date.data value }
  setMonth date value := { date with data := DateLike.setMonth date.data value }
  setDay date value := { date with data := DateLike.setDay date.data value }

instance : TimeLike (DateTime tz) where
  hour := TimeLike.hour ∘ DateTime.data
  minute := TimeLike.minute ∘ DateTime.data
  second := TimeLike.second ∘ DateTime.data

  setHour date value := { date with data := TimeLike.setHour date.data value }
  setMinute date value := { date with data := TimeLike.setMinute date.data value }
  setSecond date value := { date with data := TimeLike.setSecond date.data value }

/-- Get the current local DateTime. -/
def DateTime.now (tz: TimeZone)
 : IO (DateTime tz) := do
  let offset ← tz.toOffset
  let now ← NaiveDateTime.now
  return DateTime.mk (now.addSecs offset.second) offset

/-- Convert a DateTime with a time zone to an Epoch. -/
def DateTime.toEpoch (dt: DateTime tz) : Epoch :=
  dt.data.toEpoch

def DateTime.ofEpochGMT (epoch: Epoch) : DateTime .GMT :=
  DateTime.mk (NaiveDateTime.ofEpoch epoch) Offset.zero

/-- Convert an Epoch to a DateTime with a given time zone. -/
def DateTime.ofEpoch (epoch: Epoch) (tz: TimeZone) : IO (DateTime tz) :=
  DateTime.mk (NaiveDateTime.ofEpoch epoch) <$> tz.toOffset

/-- Convert a DateTime with a time zone to an RFC 3339 date and time string. -/
def DateTime.toRFC3339 (dt: DateTime tz) : String :=
    let naiveDateTime := dt.data
    let offset := if dt.offset.second ≤ 0 then -dt.offset.second else dt.offset.second
    let dateStr := s!"{naiveDateTime.date.year}-{leftPad 2 '0' $ toString naiveDateTime.date.month.val}-{leftPad 2 '0' $ toString naiveDateTime.date.day}"
    let timeStr := s!"{leftPad 2 '0' $ toString naiveDateTime.time.hour}:{leftPad 2 '0' $ toString naiveDateTime.time.minute}:{leftPad 2 '0' $ toString naiveDateTime.time.second}"
    let timezone :=
      match tz with
      | .GMT => " GMT"
      | .UTC => " UTC"
      | _ =>
        let offsetHours := leftPad 2 '0' $ toString (offset / 3600)
        let offsetMinutes := leftPad 2 '0' $ toString ((offset % 3600) / 60)
        let offsetSign := if dt.offset.second ≥ 0 then "+" else "-"
        s!"{offsetSign}{offsetHours}:{offsetMinutes}"
    s!"{dateStr}T{timeStr}{timezone}"
  where
    leftPad (n : Nat) (a : Char) (s : String) : String :=
      "".pushn a (n - s.length) ++ s

def DateTime.weekday (dt: DateTime tz) : Weekday :=
  dt.data.date.weekday
