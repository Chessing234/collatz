import Collatz.Research.DescentAtlas.Core

/-! The least class index for strict descent; the finite exceptions are exact. -/
namespace Collatz.Research.DescentAtlas

/-- Zero if the representative descends; otherwise one beyond the quotient
of its excess by the coefficient gap. Relevant only for a positive gap. -/
def threshold (k r : Nat) : Nat :=
  if acceleratedOrbit k r < r then 0
  else (acceleratedOrbit k r - r) / gap k r + 1

/-- Exact cutoff, with no estimate and no hidden convergence hypothesis. -/
theorem descent_iff_threshold {k r m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r ↔
      threshold k r ≤ m := by
  rw [descent_iff_gap h]
  unfold threshold
  by_cases he : acceleratedOrbit k r < r
  · rw [if_pos he]
    omega
  · rw [if_neg he]
    have hg : 0 < gap k r := by unfold gap; omega
    have hdiv := Nat.div_lt_iff_lt_mul (x := acceleratedOrbit k r - r) (y := m) hg
    rw [Nat.mul_comm m (gap k r)] at hdiv
    constructor
    · intro hd
      have hs : acceleratedOrbit k r - r < gap k r * m := by omega
      have := hdiv.mpr hs
      omega
    · intro hm
      have hd : (acceleratedOrbit k r - r) / gap k r < m := by omega
      have := hdiv.mp hd
      omega

/-- The first successful index really descends. -/
theorem descent_at_threshold {k r : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * threshold k r + r) <
      2 ^ k * threshold k r + r :=
  (descent_iff_threshold h).2 (Nat.le_refl _)

/-- Every smaller index is a rigorously certified exception at this horizon. -/
theorem no_descent_below_threshold {k r m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k) (hm : m < threshold k r) :
    2 ^ k * m + r ≤ acceleratedOrbit k (2 ^ k * m + r) := by
  have hn : ¬ acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
    intro hd
    have := (descent_iff_threshold h).1 hd
    omega
  omega

/-- A sharp warning against discarding the additive term: 7 contracts in
coefficient after eight steps, but only its positive class indices descend. -/
theorem class_seven_exact (m : Nat) :
    acceleratedOrbit 8 (256 * m + 7) < 256 * m + 7 ↔ 1 ≤ m := by
  have h : 3 ^ oddCount 7 8 < 2 ^ 8 := by decide
  have ht : threshold 8 7 = 1 := by decide
  have hh := descent_iff_threshold (m := m) h
  rw [ht] at hh
  exact hh

/-- The atlas has an explicit unresolved infinite class at its fixed horizon. -/
theorem surviving_class (m : Nat) :
    16384 * m + 16383 ≤ acceleratedOrbit 14 (16384 * m + 16383) := by
  apply no_descent_of_noncontracting (k := 14) (r := 16383) (m := m)
  · decide
  · decide

end Collatz.Research.DescentAtlas
