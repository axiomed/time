namespace Time

abbrev Epoch := Fin 253402300800

def Epoch.ofNat (n: Nat) (p: n < 253402300800 := by decide) : Epoch := ⟨n, p⟩

namespace Constants

/-- Useful constants for Epoch manipulation -/

def firstJanuary2000 := Epoch.ofNat 946684800
def secondsInDay := Epoch.ofNat 86400
def leapYearEpoch := 11017
def daysPer400Y := 365 * 400 + 97
def daysPer100Y := 365 * 100 + 24
def daysPer4Y := 365 * 4 + 1

end Constants
