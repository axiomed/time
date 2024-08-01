/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data.Int
import Time.Classes

set_option linter.all true in

/--
A `Bounded` is represented by an `Int` that is contrained by a lower and higher bounded using some
relation `rel`. It includes all the integers that `rel lo val ∧ rel val hi`.
-/
def Bounded (rel : Int → Int → Prop) (lo : Int) (hi : Int) := { val : Int // rel lo val ∧ rel val hi}

instance : LE (Bounded LE.le n m) where
  le l r := l.val ≤ r.val

instance : LT (Bounded LE.le n m) where
  lt l r := l.val < r.val

instance : Repr (Bounded rel m n) where
  reprPrec n := reprPrec n.val

instance : BEq (Bounded rel n m) where
  beq x y := (x.val = y.val)

namespace Bounded

/--
A `Bounded` integer that the relation used is the the less-equal relation so, it includes all
integers that `lo ≤ val ≤ hi`.
-/
abbrev LE := @Bounded LE.le

instance [Le lo n] [Le n hi] : OfNat (Bounded.LE lo hi) n where
  ofNat := ⟨n, And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr Le.p)⟩

instance [Le lo hi] : Inhabited (Bounded.LE lo hi) where
  default := ⟨lo, And.intro (Int.le_refl lo) (Int.ofNat_le.mpr Le.p)⟩

/--
A `Bounded` integer that the relation used is the the less-than relation so, it includes all
integers that `lo < val < hi`.
-/
abbrev LT := @Bounded LT.lt

/--
Creates a new `Bounded` Integer.
-/
@[inline]
def mk {rel : Int → Int → Prop} (val : Int) (proof : rel lo val ∧ rel val hi) : @Bounded rel lo hi :=
  ⟨val, proof⟩

namespace LE

/--
Creates a new `Bounded` integer that the relation is less-equal.
-/
@[inline]
def mk (val : Int) (proof : lo ≤ val ∧ val ≤ hi) : Bounded.LE lo hi :=
  ⟨val, proof⟩

/--
Convert a `Nat` to a `Bounded.LE`.
-/
@[inline]
def ofNat (val : Nat) (h : val ≤ hi) : Bounded.LE 0 hi :=
  Bounded.mk val (And.intro (Int.ofNat_zero_le val) (Int.ofNat_le.mpr h))

/--
Convert a `Nat` to a `Bounded.LE` using the lower boundary too.
-/
@[inline]
def ofNat' (val : Nat) (h : lo ≤ val ∧ val ≤ hi) : Bounded.LE lo hi :=
  Bounded.mk val (And.intro (Int.ofNat_le.mpr h.left) (Int.ofNat_le.mpr h.right))

/--
Convert a `Nat` to a `Bounded.LE` using the lower boundary too.
-/
@[inline]
def force (val : Int) (h : lo ≤ hi) : Bounded.LE lo hi :=
  if h₀ : lo ≤ val then
    if h₁ : val ≤ hi
      then ⟨val, And.intro h₀ h₁⟩
      else ⟨hi, And.intro h (Int.le_refl hi)⟩
  else ⟨lo, And.intro (Int.le_refl lo) h⟩

/--
Convert a `Nat` to a `Bounded.LE` using the lower boundary too.
-/
@[inline]
def force! [Le lo hi] (val : Int) : Bounded.LE lo hi :=
  if h₀ : lo ≤ val then
    if h₁ : val ≤ hi
      then ⟨val, And.intro h₀ h₁⟩
      else panic! "greater than hi"
  else panic! "lower than lo"

/--
Convert a `Bounded.LE` to a Nat.
-/
@[inline]
def toNat (n : Bounded.LE lo hi) : Nat :=
  n.val.toNat

/--
Convert a `Bounded.LE` to a Nat.
-/
@[inline]
def toNat' (n : Bounded.LE lo hi) (h : lo ≥ 0) : Nat :=
  let h₁ := (Int.le_trans h n.property.left)
  match n.val, h₁ with
  | .ofNat n, _ => n
  | .negSucc _, h => nomatch h

/--
Convert a `Bounded.LE` to an Int.
-/
@[inline]
def toInt (n : Bounded.LE lo hi) : Int :=
  n.val

/--
Convert a `Bounded.LE` to a `Fin`.
-/
@[inline]
def toFin (n : Bounded.LE lo hi) (h₀ : 0 ≤ lo) (h₁ : lo < hi) : Fin (hi + 1).toNat := by
  let h := n.property.right
  let h₁ := Int.le_trans h₀ n.property.left
  refine ⟨n.val.toNat, (Int.toNat_lt h₁).mpr ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  exact Int.lt_add_one_of_le h

/--
Convert a `Fin` to a `Bounded.LE`.
-/
@[inline]
def ofFin (fin : Fin (Nat.succ hi)) : Bounded.LE 0 hi :=
  ofNat fin.val (Nat.le_of_lt_succ fin.isLt)

/--
Convert a `Fin` to a `Bounded.LE`.
-/
@[inline]
def ofFin' {lo : Nat} (fin : Fin (Nat.succ hi)) (h : lo ≤ hi) : Bounded.LE lo hi :=
  if h₁ : fin.val ≥ lo
    then ofNat' fin.val (And.intro h₁ ((Nat.le_of_lt_succ fin.isLt)))
    else ofNat' lo (And.intro (Nat.le_refl lo) h)

/--
Creates a new `Bounded.LE` using a the modulus of a number.
-/
@[inline]
def byMod (b : Int) (i : Int) (hi : i > 0) : Bounded.LE 0 (i - 1) := by
  refine ⟨b % i, And.intro ?_ ?_⟩
  · apply Int.emod_nonneg b
    intro a
    simp_all [Int.lt_irrefl]
  · apply Int.le_of_lt_add_one
    simp [Int.add_sub_assoc]
    exact Int.emod_lt_of_pos b hi

/--
Adjust the bounds of a `Bounded` by adding a constant value to both the lower and upper bounds.
-/
@[inline]
def truncate (bounded : Bounded.LE n m) : Bounded.LE 0 (m - n) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val - n, And.intro ?_ ?_⟩
  all_goals omega

/--
Adjust the bounds of a `Bounded` by adding a constant value to both the lower and upper bounds.
-/
@[inline]
def add (bounded : Bounded.LE n m) (num : Int) : Bounded.LE (n + num) (m + num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  all_goals apply (Int.add_le_add · (Int.le_refl num))
  · exact left
  · exact right

/--
Adjust the bounds of a `Bounded` by subtracting a constant value to both the lower and upper bounds.
-/
@[inline]
def sub (bounded : Bounded.LE n m) (num : Int) : Bounded.LE (n - num) (m - num) :=
  add bounded (-num)

/--
Adjust the bounds of a `Bounded` by applying the mod operation constraining the lower bound to 0 and
the upper bound to the value.
-/
@[inline]
def mod (bounded : Bounded.LE n num) (num : Int) (hi : 0 < num) : Bounded.LE 0 (num - 1) :=
  byMod bounded.val num hi

/--
Adjust the bounds of a `Bounded` by applying the div operation.
-/
def div (bounded : Bounded.LE n m) (num : Int) (h: num > 0) : Bounded.LE (n / num) (m / num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val / num, And.intro ?_ ?_⟩
  apply Int.ediv_le_ediv
  · exact h
  · exact left
  · apply Int.ediv_le_ediv
    · exact h
    · exact right

end LE
end Bounded
