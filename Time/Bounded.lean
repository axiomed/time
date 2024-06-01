
namespace Fin

def byMod (x: Nat) (y: Nat) (h₁: y > 0 := by decide) : Fin y :=
  ⟨x % y, by simp [Nat.mod_lt x h₁]⟩

def divMax (x: Fin n) (y: Nat) (div: 0 < y := by decide) (divv: y ∣ n := by decide) : Fin (n/y) := by
  refine ⟨x.val / y, ?_⟩
  let t := Nat.div_lt_iff_lt_mul div (x := x) (y := n/y)
  apply t.mpr
  simp [Nat.div_mul_cancel (m := n) (n := y) divv]

def addMax (x: Fin n) (y: Fin m) : Fin (n + m) :=
  ⟨x.val + y.val, Nat.add_lt_add x.isLt y.isLt⟩

theorem boundaries {x y z : Nat} (h₁ : x > y) (h₂ : x < y + z) (h₃ : z ≠ 0) : x - y < z :=
  match x, y, z with
  | 0, 0, z + 1 => by
    simp
  | x + 1, 0, z + 1 => by
    simp at h₂
    exact h₂
  | x + 1, y + 1, z + 1 => by
    simp
    let h₂ := Nat.lt_pred_of_succ_lt h₂
    simp [Nat.add_assoc, Nat.add_comm z 1, ← Nat.add_assoc 1 1 z, Nat.add_comm 2 z] at h₂
    simp [← Nat.add_assoc y z 2] at h₂
    refine boundaries (Nat.pred_le_pred h₁) h₂ h₃

def toZero (n: x > y) : x > 0 := by
  match x with
  | n + 1 => exact Nat.zero_lt_of_ne_zero (Nat.succ_ne_zero n)

def ofBoundaries {x y : Nat} {ze: Fin z} (h₁ : x > y) (h₂ : x ≤ y + ze.val) (h₃ : z ≠ 0) : Fin z := by
  let p₁ := Nat.lt_succ_of_le h₂
  rw [← Nat.add_succ] at p₁
  let p₃ := Nat.add_lt_add_left ze.isLt y
  refine ⟨x - y, boundaries h₁ ?_ ?_⟩
  · exact Nat.le_trans (Nat.succ_le_succ h₂) p₃
  · exact h₃

end Fin

namespace Int

structure Bounded (lower: Int) (upper: Int) where
  data: Int
  bounds: data ≥ lower ∧ data < upper

def Bounded.ofFin (fin: Fin n) : Bounded 0 n := by
  refine ⟨Int.ofNat fin.val, ⟨Int.ofNat_le.mpr ?_, Int.ofNat_le.mpr ?_⟩⟩
  · exact Nat.zero_le fin.val
  · exact fin.isLt

def Bounded.toFin (bounded: Bounded 0 n) : Fin n.toNat :=
  match n, bounded.data, bounded.bounds with
  | n, .negSucc m, p => nomatch p
  | .ofNat n, .ofNat m, p => by
    refine ⟨m, Int.ofNat_lt.mp ?_⟩
    exact p.right

def Bounded.sub (bounded: Bounded n m) (num: Int) : Bounded (n - num) (m - num) := by
  refine ⟨bounded.data - num, And.intro ?_ ?_⟩
  · exact Int.sub_le_sub_right bounded.bounds.left num
  · exact Int.sub_lt_sub_right bounded.bounds.right num

end Int

namespace Nat

theorem neq_zero {n m : Nat} (h: n < m) : m - n ≠ 0 := by
  match m with
  | m₁ + 1 =>
    rw [Nat.add_one, Nat.succ_sub]
    · exact λh => nomatch h
    · exact Nat.le_of_lt_succ h

theorem weaken {n m : Nat} (h: n < m) : n.pred < m := by
  match n with
  | 0 => exact h
  | n + 1 => exact Nat.le_of_succ_le h

theorem weakenSub {n m k : Nat} (h: n < m) : n - k < m := by
  match k with
  | 0 => exact h
  | k + 1 =>
    simp [Nat.sub_add_eq]
    rw [Nat.sub_one]
    refine weaken (weakenSub h)

theorem sub_le_sub {n : Nat} (h: k ≤ n) (h₂: n < m) : n - k < m - k := by
  match k with
  | 0 =>
    exact h₂
  | k + 1 =>
    simp [Nat.sub_add_eq]
    rw [Nat.sub_one, Nat.sub_one]
    apply Nat.lt_of_succ_lt_succ
    let h₁ := Nat.lt_trans h h₂
    rw [Nat.succ_pred, Nat.succ_pred]
    · exact sub_le_sub (Nat.le_of_succ_le h) h₂
    · exact neq_zero (Nat.le_trans (by simp [Nat.le_succ_of_le]) h₁)
    · exact neq_zero (Nat.le_trans (by simp [Nat.le_succ_of_le]) h)

structure Bounded (lower: Nat) (upper: Nat) where
  val: Nat
  bounds: val ≥ lower ∧ val < upper

instance : Repr (Bounded m n) where
  reprPrec n p := reprPrec n.val p

def Bounded.addMax (bounded: Bounded n m) (num: Nat) : Bounded (n + num) (m + num) := by
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  · exact Nat.add_le_add bounded.bounds.left (Nat.le_refl num)
  · exact Nat.add_lt_add_right bounded.bounds.right num

instance : Repr (Bounded n m) where
  reprPrec x i := reprPrec x.val i

def Bounded.ofFin (fin: Fin n) : Bounded 0 n := by
  refine ⟨fin.val, And.intro ?_ fin.isLt⟩
  exact Nat.zero_le fin

def Bounded.toFin (bounded: Bounded n m) : Fin (m - n) := by
  refine ⟨bounded.val - n, ?_⟩
  let h₁ := bounded.bounds.left
  let h₂ := bounded.bounds.right
  apply sub_le_sub
  · simp at h₁
    exact h₁
  · exact h₂

end Nat
