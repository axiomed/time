/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Time.Time
import Time.Date

open Date Time

def seconds : Second.Offset := 604800

def minutes : Minute.Offset := 180

def days : Day.Offset := 1

def l : Second.Offset := days.convert

def h : Day.Offset := seconds.convert

#eval l
