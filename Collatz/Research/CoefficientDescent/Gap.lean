import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- Finite arithmetic: 6701 dominates every possible first-crossing failure through 256. -/
theorem gap_table_256 : ∀ k : Fin 257, ∀ a : Fin (k.val + 1),
    3 ^ a.val < 2 ^ k.val →
      a.val * 3 ^ a.val < 3 * (2 ^ k.val - 3 ^ a.val) * 6701 := by
  decide

/-- Unpack the finite certificate into the generic horizon interface. -/
theorem gap_bound_256 : GapBound 256 6701 := by
  intro k a hk ha hl
  exact gap_table_256 ⟨k, by omega⟩ ⟨a, by change a < k + 1; omega⟩ hl

/-- The cap cannot be decreased for this uniform arithmetic bound: the critical pair is (233,147). -/
theorem gap_bound_6700_fails : ¬ GapBound 256 6700 := by
  intro h
  have hh := h 233 147 (by decide) (by decide) (by decide)
  have hn : ¬ ((147 : Nat) * 3 ^ 147 < 3 * (2 ^ 233 - 3 ^ 147) * 6700) := by decide
  exact hn hh

end Collatz.Research.CoefficientDescent
