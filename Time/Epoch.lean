import Time.IO
import Time.Interval
import Time.Constants

namespace Time

/-- Epoch time as a bounded natural number. -/
def Epoch := Nat

/-- Get the current Epoch time by fetching the current number of second since the Unix epoch. -/
def Epoch.now : IO Epoch :=
  Time.primGetCurrentEpochSeconds
