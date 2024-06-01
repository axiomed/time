import Time.Bounded

namespace Time

/-! This module provides an implementation of Time-like structures, which include representations
for hours, minutes, and seconds within valid bounds. -/

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

/-- The `TimeLike` typeclass abstracts the concept of time representations that have hours, minutes,
and seconds.-/
class TimeLike (α: Type) where
  hours: α → Hour
  seconds: α → Second
  minutes: α → Minute

/-- A concrete representation of time using hours, minutes, and seconds. -/
structure Time where
  hours: Hour
  seconds: Second
  minutes: Minute
  deriving Repr

instance : TimeLike Time where
  hours t := t.hours
  minutes t := t.minutes
  seconds t := t.seconds
