import Time.Epoch
import Time.Date
import Time.Time

namespace Time

open Time.Constants

/-- Naive date without UTC -/
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
  let mut mon : Fin 12 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat (Int.toNat remDays + 1)

  if mon.val + 2 > 12 then
    year := year + 1
    mon := mon - 10
  else
    mon := mon + 2

  return {
    date := { year := Int.toNat year, month := ⟨mon.val, sorry⟩, day := ⟨mday.val, sorry⟩ },
    time := { seconds, minutes, hours }
  }
