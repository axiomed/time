import LeanCopilot

structure Constant (n : Int)

instance : CoeDep Int n (Constant n) where
  coe := Constant.mk

instance : CoeDep Nat n (Constant n) where
  coe := Constant.mk

instance (n : Nat) : OfNat (Constant n) n where
  ofNat := Constant.mk

/--
A [Bounded] in Lean is represented as a subset of natural numbers constrained by a lower and an
upper bound. Specifically, it includes all natural numbers `val` such that `lower ≤ val < upper`.
-/
def Bounded (lower upper : Int) := { val : Int // val ≥ lower ∧ val < upper }

/-- Force the int to be on the bounded. -/
def Bounded.force (n : Int) (h : lower < upper := by decide) : Bounded lower upper := by
  if h₀ : n < lower then
    if h₁ : n ≥ upper
      then omega
      else refine ⟨lower, ?_⟩; omega
  else
    if h₁ : n ≥ upper
      then refine ⟨upper - 1, And.intro ?_ ?_⟩ ; all_goals omega
      else refine ⟨n, And.intro (Int.not_lt.mp h₀) (Int.not_le.mp h₁)⟩

/-- Returns the upper bound. -/
@[inline]
def Bounded.max (_ : Bounded lower upper) : Int := upper

/-- Returns the lower bound. -/
@[inline]
def Bounded.min (_ : Bounded lower upper) : Int := lower

instance : LE (Bounded n m) where
  le l r := l.val < r.val

instance : Repr (Bounded m n) where
  reprPrec n := reprPrec n.val

instance : BEq (Bounded n m) where
  beq x y := (x.val = y.val)

/-- Theorem stating that the upper bound is non-negative for a [Bounded] starting from 0. -/
private theorem Bounded.max_gt_zero (bounded : Bounded 0 n) : n ≥ 0 := by
  let ⟨left, right⟩ := bounded.property
  simp_all only [ge_iff_le, gt_iff_lt]
  omega

@[inline, specialize]
def Bounded.ofNat (n : Nat) (proof : n ≥ lower ∧ n < upper) : Bounded lower upper :=
  ⟨n, by omega⟩

/-- Convert a [Bounded] with lower bound greater or equal than 0 to a [Nat] type. -/

@[inline, specialize]
def Bounded.toNat (bounded : Bounded lower n) (h₀ : lower ≥ 0) : Nat :=
  if h : bounded.val ≥ 0 then
    bounded.val.toNat
  else by
    let h₂ := Int.le_trans h₀ bounded.property.left
    contradiction

/-- Convert a [Bounded] with lower bound 0 to a [Fin] type. -/

@[inline, specialize]
def Bounded.toFin (bounded : Bounded lower n) (h : lower ≥ 0) : Fin n.toNat := by
  have ⟨left, right⟩ := bounded.property
  have h : bounded.val ≥ 0 := by
    simp_all only [gt_iff_lt, ge_iff_le]
    omega
  refine ⟨bounded.val.toNat, ?_⟩
  simp [Int.toNat]
  split
  all_goals split
  all_goals try simp_all only [Int.ofNat_pos, Int.ofNat_eq_coe, Int.ofNat_lt, Int.negSucc_not_pos]
  norm_cast at right
  · simp_all only [ge_iff_le, Int.negSucc_not_nonneg]
  · contradiction

/-- Transform a [Fin] into a [Bounded] that starts on 0. -/
@[inline, specialize]
def Bounded.ofFin (fin : Fin n) : Bounded 0 n :=
  ⟨fin.val, by omega⟩

/-- Adjust the bounds of a [Bounded] by adding a constant value to both the lower and upper bounds. -/
@[inline, specialize]
def Bounded.add (bounded : Bounded n m) (num : Int) : Bounded (n + num) (m + num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val + num, ?_⟩
  apply And.intro
  all_goals omega

@[inline, specialize]
def Bounded.sub (bounded : Bounded n m) (num : Int) : Bounded (n - num) (m - num) :=
  Bounded.add bounded (-num)

/-- Adjust the bounds of a [Bounded] by multiplying both the lower and upper bounds by a positive constant. -/
@[inline, specialize]
def Bounded.mul (bounded : Bounded n m) (num : Nat) (h : num > 0 := by decide) (h₁ : bounded.val ≥ 0) : Bounded (n * num) (m * num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val * num, And.intro ?_ ?_⟩
  · simp_all only [gt_iff_lt]
    apply Int.mul_le_mul
    all_goals try simp_all
    exact mod_cast Nat.zero_le _
  · simp_all [gt_iff_lt]
    apply Int.mul_lt_mul_of_pos_right
    all_goals simp_all

@[inline, specialize]
def Bounded.div (bounded : Bounded n m) (num : Int) (h: num > 0) (div : num ∣ m) : Bounded (n / num) (m / num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val / num, And.intro ?_ ?_⟩
  apply Int.ediv_le_ediv
  · exact h
  · exact left
  · apply (Int.ediv_lt_iff_lt_mul h).mpr
    simp_all [Int.ediv_mul_cancel div]

@[inline, specialize]
def Bounded.byMod (b : Int) (i : Int) (hi : 0 < i) : Bounded 0 i := by
  refine ⟨b % i, And.intro ?_ ?_⟩
  · apply Int.emod_nonneg
    intro a
    simp_all [Int.lt_irrefl]
  · exact Int.emod_lt_of_pos _ hi

@[inline, specialize]
def Bounded.mod (b : Bounded n m) (i : Int) (hi : 0 < i) : Bounded 0 i :=
  Bounded.byMod b.val i hi

@[inline, specialize]
def Fin.ofBoundaries {x y : Nat} {ze : Fin z} (h₁ : x > y) (h₂ : x ≤ y + ze.val) : Fin z := by
  refine ⟨x - y, ?_⟩
  omega
