import Collatz.Strategy.FirstLightScan

/-! Completeness and budget monotonicity for the stateful crossing checker. -/
namespace Collatz.FirstLightScan
open FirstLightDescent

/-- A first-crossing descent within the searched interval is always found. -/
theorem scan_complete (n fuel k j : Nat) (hkj : k≤j) (hj : j<k+fuel)
    (hf : FirstLight n j) (hd : acceleratedOrbit j n < n) :
    scan n fuel k (acceleratedOrbit k n) (oddCount n k) = true := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    by_cases he : k=j
    · subst he
      simp only [scan, if_pos hf.1, decide_eq_true_eq]
      exact hd
    · have hpre := hf.2 k (by omega)
      have hnot : ¬ 3^oddCount n k < 2^k := by omega
      rw [scan, if_neg hnot, ← acceleratedOrbit_succ_step, ← Density.oddCount_succ_last]
      exact ih (k+1) (by omega) (by omega)

/-- The executable test is exactly the bounded first-crossing descent property. -/
theorem check_iff (H n : Nat) :
    check H n = true ↔
      ∃ k : Fin (H+1), FirstLight n k.val ∧ acceleratedOrbit k.val n < n := by
  constructor
  · exact check_sound H n
  · intro ⟨k, hf, hd⟩
    exact scan_complete n (H+1) 0 k.val (by omega) (by simpa only [Nat.zero_add] using k.isLt) hf hd

/-- Enlarging a successful horizon never changes success to failure. -/
theorem check_mono {H K n : Nat} (hHK : H≤K) (h : check H n = true) :
    check K n = true := by
  obtain ⟨j, hf, hd⟩ := check_sound H n h
  exact (check_iff K n).mpr ⟨⟨j.val, by have := j.isLt; omega⟩, hf, hd⟩

/-- No positive-time crossing is searched when the horizon is zero. -/
theorem check_zero_horizon (n : Nat) : check 0 n = false := rfl

/-- Boundary regression: start 3 first crosses and descends at index 4. -/
theorem check_three_boundary : check 3 3 = false ∧ check 4 3 = true := by decide

/-- The trivial orbit does not strictly descend, despite its coefficient crossing. -/
theorem check_one_not_descent : check 10 1 = false := by decide

end Collatz.FirstLightScan
