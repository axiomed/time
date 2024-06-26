namespace Time

structure Interval (lower: Nat) (upper: Nat) where
  val: Nat
  bounds: val ≥ lower ∧ val < upper
  deriving BEq

instance : Repr (Interval m n) where
  reprPrec n p := reprPrec n.val p

def Interval.addMax (bounded: Interval n m) (num: Nat) : Interval (n + num) (m + num) := by
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  · exact Nat.add_le_add bounded.bounds.left (Nat.le_refl num)
  · exact Nat.add_lt_add_right bounded.bounds.right num

instance : Repr (Interval n m) where
  reprPrec x i := reprPrec x.val i

def Interval.ofFin (fin: Fin n) : Interval 0 n := by
  refine ⟨fin.val, And.intro ?_ fin.isLt⟩
  exact Nat.zero_le fin

theorem neq_zero {n m : Nat} (h: n < m) : m - n ≠ 0 := by
  match m with
  | m₁ + 1 =>
    rw [Nat.add_one, Nat.succ_sub]
    · exact λh => nomatch h
    · exact Nat.le_of_lt_succ h

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

def Interval.toFin (bounded: Interval n m) : Fin (m - n) := by
  refine ⟨bounded.val - n, ?_⟩
  apply sub_le_sub
  · exact bounded.bounds.left
  · exact bounded.bounds.right

def Interval.ofNat? (val: Nat) : Option (Interval lower upper) :=
  if h: val ≥ lower ∧ val < upper
    then Interval.mk val h
    else none

def Fin.byMod (x: Nat) (y: Nat) (h₁: y > 0 := by decide) (h₂: y ≤ z := by decide) : Fin z :=
  let h₃ := Nat.mod_lt x h₁
  ⟨x % y, Nat.lt_of_lt_of_le h₃ h₂⟩

private theorem boundaries {x y z : Nat} (h₁ : x > y) (h₂ : x < y + z) (h₃ : z ≠ 0) : x - y < z :=
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

def Fin.ofBoundaries {x y : Nat} {ze: Fin z} (h₁ : x > y) (h₂ : x ≤ y + ze.val) (h₃ : z ≠ 0) : Fin z := by
  let p₁ := Nat.lt_succ_of_le h₂
  rw [← Nat.add_succ] at p₁
  let p₃ := Nat.add_lt_add_left ze.isLt y
  refine ⟨x - y, boundaries h₁ ?_ ?_⟩
  · exact Nat.le_trans (Nat.succ_le_succ h₂) p₃
  · exact h₃

def Fin.ofNat? (x: Nat) : Option (Fin n) :=
  if h : x < n
    then some ⟨x, h⟩
    else none
