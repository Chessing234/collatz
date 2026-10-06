import Collatz.Strategy.FirstLightDescent

/-!
# A stateful first-coefficient-crossing checker

The scanner carries the current orbit value and odd count. It never recomputes
all preceding prefixes. Soundness reconstructs the exact FirstLight predicate
and a strict descent witness, so a finite Boolean certificate can replace the
much more expensive nested finite existential search.
-/

namespace Collatz.FirstLightScan
open FirstLightDescent

/-- Search the next `fuel` indices, including the supplied current index.
At the first coefficient crossing, return whether the orbit has descended. -/
def scan (n : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel+1, k, x, a =>
    if 3^a < 2^k then decide (x<n)
    else scan n fuel (k+1) (acceleratedStep x) (a+x%2)

/-- Soundness with the prefix invariant made explicit. -/
theorem scan_sound (n fuel k : Nat)
    (hprefix : ∀ j, j<k → 2^j ≤ 3^oddCount n j)
    (hs : scan n fuel k (acceleratedOrbit k n) (oddCount n k) = true) :
    ∃ j, k ≤ j ∧ j < k+fuel ∧ FirstLight n j ∧ acceleratedOrbit j n < n := by
  induction fuel generalizing k with
  | zero => simp [scan] at hs
  | succ fuel ih =>
    by_cases hl : 3^oddCount n k < 2^k
    · have hd : acceleratedOrbit k n < n := by
        simpa only [scan, if_pos hl, decide_eq_true_eq] using hs
      exact ⟨k, Nat.le_refl k, by omega, ⟨hl,hprefix⟩, hd⟩
    · have hnext : scan n fuel (k+1) (acceleratedOrbit (k+1) n) (oddCount n (k+1)) = true := by
        rw [scan, if_neg hl] at hs
        simpa only [acceleratedOrbit_succ_step, Density.oddCount_succ_last] using hs
      have hp : ∀ j, j<k+1 → 2^j ≤ 3^oddCount n j := by
        intro j hj
        by_cases hlt : j<k
        · exact hprefix j hlt
        · have he : j=k := by omega
          subst he
          omega
      obtain ⟨j, hkj, hj, hfirst, hd⟩ := ih (k+1) hp hnext
      exact ⟨j, by omega, by omega, hfirst, hd⟩

/-- Scan the actual orbit at indices 0 through H inclusive. -/
def check (H n : Nat) : Bool := scan n (H+1) 0 n 0

/-- A successful check gives an exact first-crossing descent by the horizon. -/
theorem check_sound (H n : Nat) (h : check H n = true) :
    ∃ k : Fin (H+1), FirstLight n k.val ∧ acceleratedOrbit k.val n < n := by
  have hs : scan n (H+1) 0 (acceleratedOrbit 0 n) (oddCount n 0) = true := h
  obtain ⟨j, _, hj, hf, hd⟩ := scan_sound n (H+1) 0 (by intro j hj; omega) hs
  exact ⟨⟨j, by omega⟩, hf, hd⟩

/-- Finite certificate for an initial range, skipping the excluded starts 0 and 1. -/
def checkRange (H N : Nat) : Bool :=
  (List.range N).all fun n => n≤1 || check H n

/-- Range certificates feed directly into the generic first-crossing theorem. -/
theorem checkRange_sound (H N : Nat) (h : checkRange H N = true) :
    ∀ n : Fin N, 1<n.val →
      ∃ k : Fin (H+1), FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val := by
  intro n hn
  have hall := List.all_eq_true.mp h n.val (List.mem_range.mpr n.isLt)
  have hc : check H n.val = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, show ¬n.val≤1 by omega, false_or] using hall
  exact check_sound H n.val hc

end Collatz.FirstLightScan
