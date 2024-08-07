/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Time.Zoned.Database.TzIf
import Time.Zoned.TimeZone
import Time.DateTime

namespace Std
namespace Time
namespace TimeZone
namespace Database
open TZif

/--
Function to convert LocalTimeType to Offset
-/
def localTimeTypeToOffset (localTimeType : LocalTimeType) : Offset :=
  Offset.ofSeconds (Internal.UnitVal.ofInt localTimeType.gmtOffset)

/--
Find the current timestamp.
-/
def findLocalTimeType (timestamp : Timestamp) (tzif : TZifV1) : Option LocalTimeType := do
  -- This is a simplified example; actual implementation should handle
  -- finding the correct LocalTimeType based on the timestamp and transition times.
  if !tzif.transitionTimes.isEmpty && !tzif.localTimeTypes.isEmpty then
    if let some idx := tzif.transitionTimes.findIdx? (λ t => t > timestamp.val) then
      let idx := tzif.transitionIndices.get! (idx - 1) |>.toNat
      tzif.localTimeTypes.get! idx
    else
      tzif.localTimeTypes.back
  else none

/-
This.
-/
def tzifV1ToTimeZoneAt (timestamp : Timestamp) (tzif : TZifV1) : Option TimeZone := do
  let localTimeType ← findLocalTimeType timestamp tzif
  dbg_trace s!"{repr localTimeType}"
  let offset := localTimeTypeToOffset localTimeType
  let abbreviationIndex := localTimeType.abbreviationIndex
  dbg_trace s!"{repr tzif.abbreviations}"
  let abbreviation := tzif.abbreviations.getD abbreviationIndex.toNat "Unknown"
  some { offset := offset, name := abbreviation }

def t : IO Unit := do
  let tm : Timestamp := 1192330900
  let tz1 ← IO.FS.readBinFile "/etc/localtime"
  let tz1 := (TZif.parse.run tz1).toOption.get!
  let data := tzifV1ToTimeZoneAt tm tz1.v1
  dbg_trace s!"{repr data}"
  pure ()
