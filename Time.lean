import LeanCopilot

/-- The range of possible hours for a time zone offset. -/
def SpanZoneOffset.Hour := Fin 24

/-- The range of possible minutes for a time zone offset. -/
def SpanZoneOffset.Minute := Fin 60

/-- The range of possible seconds for a time zone offset. -/
def SpanZoneOffset.Second := Fin 60

/-- Possible seconds in a time zone offset. -/
def SpanZoneOffset := Bounded (-86399) 86399

/-- The range of Unix seconds supported with SpanZoneOffset. -/
def UnixSeconds := Bounded (-377705116800 - 86399) (253402300799 - 86399)

/-- The sign is a structure that holds -1 for negative, 0 for no sign and 1 for positive. -/
def Sign := Bounded (-1) 2

/-- Gets the sign of an [Int]. -/
def Sign.ofInt (val : Int) : Sign := by
  refine ⟨val.sign, ?_⟩
  simp [Int.sign]
  split
  all_goals simp

/-- The range of ISO years supported. -/
def ISOYear := Bounded (-9999) 10000

/-- The range of ISO week values. -/
def ISOWeek := Bounded 1 54
