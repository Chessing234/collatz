import Collatz.Exploration.FloorProductError

/-! Finite descent from odd count and source-dependent floor factors.
No individual odd-state product is required by this sufficient criterion. -/
namespace Collatz.Exploration.FloorProductDescent
open FloorAffineError FloorProductError

/-- The floor-product criterion forces descent somewhere before the selected endpoint. -/
theorem descent_before {n j : Nat} (hn : 0 < n)
    (hs : 3^oddCount n j*weight n^oddCount n j <
      2^j*base n^oddCount n j) :
    ∃ i, i ≤ j ∧ acceleratedOrbit i n < n := by
  apply Classical.byContradiction
  intro hno
  have hf : ∀ i, i ≤ j → n ≤ acceleratedOrbit i n := by
    intro i hi
    by_cases hd : acceleratedOrbit i n < n
    · exact False.elim (hno ⟨i,hi,hd⟩)
    · omega
  have hb := product_band_budget (n := n) (b := n) (a := j) (c := 0)
    (P := 1) (Q := 1) hn (fun i hi => hf i (by omega)) (hf j (by omega)) (by simp)
  have hbound : 2^j*base n^oddCount n j ≤
      3^oddCount n j*weight n^oddCount n j := by simpa using hb
  omega

/-- Certified descent transfers to the ordinary orbit with an explicit time bound. -/
theorem standard_descent_before {n j : Nat} (hn : 0 < n)
    (hs : 3^oddCount n j*weight n^oddCount n j <
      2^j*base n^oddCount n j) :
    ∃ t, t ≤ 2*j ∧ orbit t n < n := by
  obtain ⟨i,hi,hd⟩ := descent_before hn hs
  refine ⟨TimeChange.clock n i,?_,?_⟩
  · have ht := (TimeChange.clock_bounds n i).2
    omega
  · rw [TimeChange.orbit_at_clock]
    exact hd

end Collatz.Exploration.FloorProductDescent
