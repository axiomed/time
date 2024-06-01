import Time.Time

namespace Time

structure Interval where
  secs: Nat
  nanos: Nat

structure Duration where
  secs: Nat
  nanos: Nat

def Duration.ofSecs (seconds: Second) : Duration :=
  { secs := seconds.val, nanos := 0 }

def Duration.ofMinutes (minutes: Minute) : Duration :=
  { secs := minutes * 60, nanos := 0 }

def Duration.ofHours (hours: Hour) : Duration :=
  { secs := hours * 3600, nanos := 0 }

def Duration.ofTime (time: Time) : Duration :=
  { secs := TimeLike.hours time * 3600 + TimeLike.minutes time * 60 + TimeLike.seconds time
  , nanos := 0 }
