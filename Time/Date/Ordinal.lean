import Time.Interval

namespace Time.Date

/-- Represents a day of the year, independent of the year itself. It's defined as a bounded
natural number between 0 and 365. -/
def Ordinal (isLeap: Bool) := Time.Interval 1 (if isLeap then 367 else 366)

/-- Make a ordinal out of a Nat and a proof -/
def Ordinal.mk (data: Nat) (proof: data ≥ 1 ∧ data < (if isLeap then 367 else 366) := by decide) : Ordinal isLeap :=
  ⟨data, proof⟩
