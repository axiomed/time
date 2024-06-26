namespace Time.Date

/-- Defines the enumeration for days of the week. Each variant corresponds to a day of the week,
from Monday to Sunday. -/
inductive Weekday
  | mon
  | tue
  | wed
  | thu
  | fri
  | sat
  | sun
  deriving Repr, Inhabited, BEq

namespace Weekday

/-- Converts a `Fin 7` representing a day index into a corresponding `Weekday`. This function is
useful for mapping numerical representations to days of the week. -/
def ofFin : Fin 7 → Weekday
  | 0 => .mon
  | 1 => .tue
  | 2 => .wed
  | 3 => .thu
  | 4 => .fri
  | 5 => .sat
  | 6 => .sun

def ofNat? : Nat → Option Weekday
  | 0 => some .mon
  | 1 => some .tue
  | 2 => some .wed
  | 3 => some .thu
  | 4 => some .fri
  | 5 => some .sat
  | 6 => some .sun
  | _ => none

def ofNat! (n: Nat) : Weekday :=
  match ofNat? n with
  | some res => res
  | none     => panic! "unwrap weekday"

/-- Converts a number of days since the civil epoch to the corresponding weekday. This function
translates a day count into a day of the week. -/
def natOfDays (z: Int) : Nat :=
  if z ≥ -4
    then ((z + 4) % 7).toNat
    else ((z + 5) % 7 + 6).toNat

def ofDays : Int → Weekday :=
  ofNat! ∘ natOfDays
