import Collatz.Strategy.FirstDescentClassInterval

/-!
# Solving affine inequalities over natural class indices

Intervals are lower-inclusive and upper-exclusive. `none` is an infinite
upper endpoint; inconsistent bounds represent the empty set. All arithmetic
uses exact natural numbers, including the guarded divisions.
-/
namespace Collatz.Research.DescentIntervals

structure IndexInterval where
  lower : Nat
  upper : Option Nat
  deriving DecidableEq, Repr

def IndexInterval.Contains (I : IndexInterval) (m : Nat) : Prop :=
  I.lower ≤ m ∧ match I.upper with
    | none => True
    | some u => m < u

instance (I : IndexInterval) (m : Nat) : Decidable (I.Contains m) := by
  unfold IndexInterval.Contains
  cases I.upper <;> simp only <;> infer_instance

def allIndices : IndexInterval := ⟨0, none⟩
def noIndices : IndexInterval := ⟨0, some 0⟩

@[simp] theorem contains_all (m : Nat) : allIndices.Contains m := by
  simp [IndexInterval.Contains, allIndices]

@[simp] theorem not_contains_empty (m : Nat) : ¬ noIndices.Contains m := by
  simp [IndexInterval.Contains, noIndices]

def capUpper : Option Nat → Option Nat → Option Nat
  | none, v => v
  | u, none => u
  | some u, some v => some (min u v)

def intersect (I J : IndexInterval) : IndexInterval :=
  ⟨max I.lower J.lower, capUpper I.upper J.upper⟩

@[simp] theorem contains_intersect (I J : IndexInterval) (m : Nat) :
    (intersect I J).Contains m ↔ I.Contains m ∧ J.Contains m := by
  cases I with
  | mk l u =>
    cases J with
    | mk t v =>
      cases u <;> cases v <;>
        simp [intersect, IndexInterval.Contains, capUpper] <;> omega

/-- Solve `A*m+b ≤ C*m+d`. No restriction on the four coefficients. -/
def solveLE (A b C d : Nat) : IndexInterval :=
  if A ≤ C then
    if b ≤ d then allIndices
    else if A = C then noIndices
    else ⟨(b - d - 1) / (C - A) + 1, none⟩
  else if b ≤ d then ⟨0, some ((d - b) / (A - C) + 1)⟩
  else noIndices

/-- The increasing-gap branch is a sharp lower cutoff. -/
theorem increasing_gap_iff {A b C d m : Nat} (hs : A < C) (hb : d < b) :
    A * m + b ≤ C * m + d ↔ (b - d - 1) / (C - A) + 1 ≤ m := by
  have hg : 0 < C - A := by omega
  have hc : C = A + (C - A) := by omega
  have he : C * m = A * m + (C - A) * m := by rw [hc, Nat.add_mul]; simp
  have hd := Nat.div_lt_iff_lt_mul (x := b - d - 1) (y := m) hg
  rw [Nat.mul_comm m (C - A)] at hd
  omega

/-- The decreasing-gap branch is a sharp finite upper cutoff. -/
theorem decreasing_gap_iff {A b C d m : Nat} (hs : C < A) (hb : b ≤ d) :
    A * m + b ≤ C * m + d ↔ m < (d - b) / (A - C) + 1 := by
  have hg : 0 < A - C := by omega
  have ha : A = C + (A - C) := by omega
  have he : A * m = C * m + (A - C) * m := by rw [ha, Nat.add_mul]; simp
  have hd := Nat.le_div_iff_mul_le (x := m) (y := d - b) hg
  rw [Nat.mul_comm m (A - C)] at hd
  omega

/-- Soundness and completeness of the arithmetic solver, including empty cases. -/
theorem solveLE_spec (A b C d m : Nat) :
    (solveLE A b C d).Contains m ↔ A * m + b ≤ C * m + d := by
  unfold solveLE
  split
  next hs =>
    split
    next hb =>
      have hm := Nat.mul_le_mul_right m hs
      simp only [contains_all, true_iff]
      omega
    next hb =>
      split
      next he =>
        subst C
        simp only [not_contains_empty, false_iff]
        omega
      next he =>
        simpa [IndexInterval.Contains] using
          (increasing_gap_iff (m := m) (by omega : A < C) (by omega : d < b)).symm
  next hs =>
    split
    next hb =>
      simpa [IndexInterval.Contains] using
        (decreasing_gap_iff (m := m) (by omega : C < A) hb).symm
    next hb =>
      have hm := Nat.mul_le_mul_right m (show C ≤ A by omega)
      simp only [not_contains_empty, false_iff]
      omega

/-- Intersect finitely many exact solution sets. -/
def intersectMany : List IndexInterval → IndexInterval
  | [] => allIndices
  | I :: rest => intersect I (intersectMany rest)

theorem intersectMany_spec (L : List IndexInterval) (m : Nat) :
    (intersectMany L).Contains m ↔ ∀ I ∈ L, I.Contains m := by
  induction L with
  | nil => simp [intersectMany]
  | cons I L ih => simp [intersectMany, ih]

/-- Membership is decidable from the two endpoints, independently of orbit size. -/
def membershipB (I : IndexInterval) (m : Nat) : Bool := decide (I.Contains m)

@[simp] theorem membershipB_spec (I : IndexInterval) (m : Nat) :
    membershipB I m = true ↔ I.Contains m := by simp [membershipB]

end Collatz.Research.DescentIntervals
