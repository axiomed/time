import Time.Bounded

namespace Time

/-! This module provides an implementation of Time-like structures, which include representations
for hour, minute, and second within valid bounds. -/

/-- An hour in a day, represented as a value between 0 and 23. -/
abbrev Hour := Fin 24

/-- Constructor for `Hour` ensuring the data is within valid bounds. -/
def Hour.mk (data: Nat) (proof: data < 24 := by decide) : Hour := ⟨data, proof⟩

/-- A minute in an hour, represented as a value between 0 and 59. -/
abbrev Minute := Fin 60

/-- Constructor for `Minute` ensuring the data is within valid bounds. -/
def Minute.mk (data: Nat) (proof: data < 60 := by decide) : Minute := ⟨data, proof⟩

/-- A second in a minute, represented as a value between 0 and 59. -/
abbrev Second := Fin 60

/-- Constructor for `Second` ensuring the data is within valid bounds. -/
def Second.mk (data: Nat) (proof: data < 60 := by decide) : Second := ⟨data, proof⟩

/-- The `TimeLike` typeclass abstracts the concept of time representations that have hour, minute,
and second.-/
class TimeLike (α: Type) where
  hour: α → Hour
  second: α → Second
  minute: α → Minute

  setHour: α → Hour → α
  setSecond: α → Second → α
  setMinute: α → Minute → α

/-- A concrete representation of time using hour, minute, and second. -/
structure Time where
  hour: Hour
  minute: Minute
  second: Second
  deriving Repr, Inhabited

def Time.toSecs (time: Time) : Nat :=
  time.hour * 3600 + time.minute * 60 + time.second

def Time.ofSecs (second: Nat) : Time :=
  let h := second / 3600
  let m := (second % 3600) / 60
  let s := (second % 3600) % 60
  { hour := Fin.byMod h 24, minute := Fin.byMod m 60, second := Fin.byMod s 60 }

def Time.subSecs (time: Time) (secondsToSubtract: Nat) : Time :=
  Time.ofSecs (time.toSecs - secondsToSubtract)

def Time.addSecs (time: Time) (secondsToAdd: Int) : Time :=
  Time.ofSecs (time.toSecs + secondsToAdd).toNat

instance : TimeLike Time where
  hour t := t.hour
  minute t := t.minute
  second t := t.second

  setHour time value := { time with hour := value }
  setMinute time value := { time with minute := value }
  setSecond time value := { time with second := value }

inductive HourMarker
  | am
  | pm

def HourMarker.toAbsolute (marker: HourMarker) (time: Hour) : Hour :=
  match marker with
  | .am => time
  | .pm => time + 12
