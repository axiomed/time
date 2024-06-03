import Time.IO
import Time.Bounded
import Time.Constants

namespace Time

/-- Epoch time as a bounded natural number. -/
abbrev Epoch := Fin 253402300800

/-- Convert a natural number to an Epoch, ensuring it is within the valid range. -/
def Epoch.ofNat (n: Nat) (p: n < 253402300800 := by decide) : Epoch := ⟨n, p⟩

/-- Get the current Epoch time by fetching the current number of second since the Unix epoch. -/
def Epoch.now : IO Epoch := do
  let secs ← Time.primGetCurrentEpochSeconds
  pure ⟨secs % 253402300800, Nat.mod_lt secs (by decide)⟩

/-- Calculate the difference between two Epoch times in second. -/
def Epoch.diff (e1 e2: Epoch) : Int :=
  e1.val - e2.val

/-- Add a given number of second to an Epoch time. -/
def Epoch.addSecs (epoch: Epoch) (secs: Int) : Epoch :=
  Fin.byMod (epoch.val + secs.toNat) 253402300800
