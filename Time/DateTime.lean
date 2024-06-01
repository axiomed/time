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
  deriving Repr

instance : DateLike NaiveDateTime where
  year := Date.year ∘ NaiveDateTime.date
  month := Date.month ∘ NaiveDateTime.date
  day := Date.day ∘ NaiveDateTime.date

instance : TimeLike NaiveDateTime where
  hours := Time.hours ∘ NaiveDateTime.time
  minutes := Time.minutes ∘ NaiveDateTime.time
  seconds := Time.seconds ∘ NaiveDateTime.time

/-- Converts an Epoch to a NaiveDateTime by calculating the corresponding date and time. -/
def NaiveDateTime.ofEpoch (epoch: Epoch) : NaiveDateTime := Id.run $ do
  let daySecs : Fin 86400 := Fin.byMod epoch 86400

  let seconds := Fin.byMod daySecs 60
  let minutes := Fin.divMax (Fin.byMod daySecs 3600) 60
  let hours := Fin.divMax daySecs 3600

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
    time := { seconds, minutes, hours }
  }

def NaiveDateTime.subSecs (dt: NaiveDateTime) (secondsToSubtract: Nat) : NaiveDateTime :=
  let daysToSubtract := secondsToSubtract / 86400
  let dayToSubtract := secondsToSubtract % 86400
  let date := dt.date.subDays daysToSubtract
  if dayToSubtract > dt.time.toSecs then
    let date := date.subDays 1
    let time := Time.ofSecs (86400 - dayToSubtract)
    ⟨date, time⟩
  else
    ⟨date, dt.time.subSecs dayToSubtract⟩

/-- An enumeration representing different time zones. -/
inductive TimeZone
  | GMT
  | UTC
  | offset : Int → Int → TimeZone
  deriving Repr

structure DateTime (tz: TimeZone) where
  data: NaiveDateTime

def TimeZone.offsetInSeconds : IO Int :=
  Time.primTimeOffset

def TimeZone.offsetInHours : IO Int :=
  (· / 3600) <$> TimeZone.offsetInSeconds

def TimeZone.local : IO TimeZone := do
  let seconds ← TimeZone.offsetInSeconds
  let hours := seconds / 3600
  return TimeZone.offset hours seconds
