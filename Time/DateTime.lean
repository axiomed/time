import Time.Local.TimeZone
import Time.Epoch
import Time.Date
import Time.Time
import Time.IO

namespace Time

/-! Time manipulation utilities for Date and Time together. -/

open Time.Constants Time.Date Time.Local

/--Naive representation of date and time without considering UTC offsets. -/
structure NaiveDateTime where
  date: YMD
  time: Time
  deriving Repr, Inhabited

instance : DateLike NaiveDateTime where
  year := YMD.year ∘ NaiveDateTime.date
  month := YMD.month ∘ NaiveDateTime.date
  day := YMD.day ∘ NaiveDateTime.date

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
  let days := (YMD.civilFromDate dt.date).toNat
  let second := dt.time.toSecs
  (days * 86400 + second)

/-- Converts an Epoch to a NaiveDateTime by calculating the corresponding date and time. -/
def NaiveDateTime.ofEpoch (daySecs: Epoch) : NaiveDateTime := Id.run $ do
  let daySecs : Nat := daySecs

  let second := daySecs / 60
  let minute := (daySecs % 3600) / 60
  let hour := daySecs / 3600

  let daysSinceEpoch := daySecs /86400
  let boundedDaysSinceEpoch := daysSinceEpoch

  let days := boundedDaysSinceEpoch - leapYearEpoch

  let mut quadracentennialCycles := days / daysPer400Y;
  let mut remDays := days % daysPer400Y;

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
    date := { year := Int.ofNat year, month := hmon, day := Day.ofFin mday },
    time := { second := Fin.byMod second 60, minute := Fin.byMod minute 60, hour := Fin.byMod hour 24 }
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
    ⟨date.subDays 1, Time.ofSecs (86400 + (dt.time.toSecs + dayToAdd)).toNat⟩
  else
    ⟨date, dt.time.addSecs dayToAdd⟩

/-- Get the current NaiveDateTime based on the current Epoch time. -/
def NaiveDateTime.now : IO NaiveDateTime := do
  let epoch ← Epoch.now
  return NaiveDateTime.ofEpoch epoch

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

def DateTime.weekday (dt: DateTime tz) : Weekday :=
  dt.data.date.weekday
