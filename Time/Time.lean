import Time.Bounded

namespace Time

/-- An hour in a day, represented as a value between 0 and 24. ISO format allows for 24:00:00  -/
def Hour := Fin 25
  deriving Repr, Inhabited

@[inline]
def Hour.toNat (hour: Hour) : Nat := hour.val

/-- Constructor for `Hour` ensuring the data is within valid bounds. -/
def Hour.mk (data: Nat) (proof: data < 25 := by decide) : Hour := ⟨data, proof⟩

/-- A minute in an hour, represented as a value between 0 and 50. -/
def Minute := Fin 60
  deriving Repr, Inhabited

@[inline]
def Minute.toNat (minute: Minute) : Nat := minute.val

/-- Constructor for `Minute` ensuring the data is within valid bounds. -/
def Minute.mk (data: Nat) (proof: data < 60 := by decide) : Minute := ⟨data, proof⟩

/-- A second in a minute, represented as a value between 0 and 60. Leap second counts :P -/
def Second := Fin 61
  deriving Repr, Inhabited

@[inline]
def Second.toNat (second: Second) : Nat := second.val

/-- Constructor for `Second` ensuring the data is within valid bounds. -/
def Second.mk (data: Nat) (proof: data < 61 := by decide) : Second := ⟨data, proof⟩

/-- The range of possible millisecond values. -/
def Millisecond := Fin 1000

@[inline]
def Millisecond.toNat (millisecond: Millisecond) : Nat := millisecond.val

/-- Constructor for `Millisecond` ensuring the data is within valid bounds. -/
def Millisecond.mk (data: Nat) (proof: data < 1000 := by decide) : Millisecond := ⟨data, proof⟩

/-- The range of possible microsecond values. -/
def Microsecond := Fin 1000

@[inline]
def Microsecond.toNat (microsecond: Microsecond) : Nat := microsecond.val

/-- Constructor for `Microsecond` ensuring the data is within valid bounds. -/
def Microsecond.mk (data: Nat) (proof: data < 1000 := by decide) : Microsecond := ⟨data, proof⟩

/-- The range of possible nanosecond values. -/
def Nanosecond := Fin 1000

@[inline]
def Nanosecond.toNat (nanosecond: Nanosecond) : Nat := nanosecond.val

/-- Constructor for `Nanosecond` ensuring the data is within valid bounds. -/
def Nanosecond.mk (data: Nat) (proof: data < 1000 := by decide) : Nanosecond := ⟨data, proof⟩

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
  time.hour.toNat * 3600 + time.minute.toNat * 60 + time.second.toNat

def Time.ofSecs (second: Nat) : Time :=
  let h := second / 3600
  let m := (second % 3600) / 60
  let s := (second % 3600) % 60
  { hour := Fin.ofNat h , minute := Fin.ofNat m, second := Fin.ofNat s }

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
  | .pm => Fin.ofNat (time.toNat + 12)
