import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0997

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8130. -/
theorem bounds_13_8130 : exactInterval 13 8130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8130 : oddCount 8130 13 = 9 ∧ acceleratedOrbit 13 8130 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8130) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8130.1, data_13_8130.2]

/-- Complete interval computation for depth 13, residue 8131. -/
theorem bounds_13_8131 : exactInterval 13 8131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8131 : oddCount 8131 13 = 9 ∧ acceleratedOrbit 13 8131 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8131) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8131.1, data_13_8131.2]

/-- Complete interval computation for depth 13, residue 8132. -/
theorem bounds_13_8132 : exactInterval 13 8132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8132 : oddCount 8132 13 = 6 ∧ acceleratedOrbit 13 8132 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8132) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8132.1, data_13_8132.2]

/-- Complete interval computation for depth 13, residue 8133. -/
theorem bounds_13_8133 : exactInterval 13 8133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8133 : oddCount 8133 13 = 6 ∧ acceleratedOrbit 13 8133 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8133) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8133.1, data_13_8133.2]

/-- Complete interval computation for depth 13, residue 8134. -/
theorem bounds_13_8134 : exactInterval 13 8134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8134 : oddCount 8134 13 = 6 ∧ acceleratedOrbit 13 8134 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8134) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8134.1, data_13_8134.2]

/-- Complete interval computation for depth 13, residue 8135. -/
theorem bounds_13_8135 : exactInterval 13 8135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8135 : oddCount 8135 13 = 8 ∧ acceleratedOrbit 13 8135 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8135) = 3 ^ 8 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8135.1, data_13_8135.2]

/-- Complete interval computation for depth 13, residue 8136. -/
theorem bounds_13_8136 : exactInterval 13 8136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8136 : oddCount 8136 13 = 7 ∧ acceleratedOrbit 13 8136 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8136) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8136.1, data_13_8136.2]

/-- Complete interval computation for depth 13, residue 8137. -/
theorem bounds_13_8137 : exactInterval 13 8137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8137 : oddCount 8137 13 = 8 ∧ acceleratedOrbit 13 8137 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8137) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8137.1, data_13_8137.2]

/-- Complete interval computation for depth 13, residue 8138. -/
theorem bounds_13_8138 : exactInterval 13 8138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8138 : oddCount 8138 13 = 7 ∧ acceleratedOrbit 13 8138 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8138) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8138.1, data_13_8138.2]

/-- Complete interval computation for depth 13, residue 8139. -/
theorem bounds_13_8139 : exactInterval 13 8139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8139 : oddCount 8139 13 = 5 ∧ acceleratedOrbit 13 8139 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8139) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8139.1, data_13_8139.2]

/-- Complete interval computation for depth 13, residue 8140. -/
theorem bounds_13_8140 : exactInterval 13 8140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8140 : oddCount 8140 13 = 7 ∧ acceleratedOrbit 13 8140 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8140) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8140.1, data_13_8140.2]

/-- Complete interval computation for depth 13, residue 8141. -/
theorem bounds_13_8141 : exactInterval 13 8141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8141 : oddCount 8141 13 = 7 ∧ acceleratedOrbit 13 8141 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8141) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8141.1, data_13_8141.2]

/-- Complete interval computation for depth 13, residue 8142. -/
theorem bounds_13_8142 : exactInterval 13 8142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8142 : oddCount 8142 13 = 8 ∧ acceleratedOrbit 13 8142 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8142) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8142.1, data_13_8142.2]

/-- Complete interval computation for depth 13, residue 8143. -/
theorem bounds_13_8143 : exactInterval 13 8143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8143 : oddCount 8143 13 = 8 ∧ acceleratedOrbit 13 8143 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8143) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8143.1, data_13_8143.2]

/-- Complete interval computation for depth 13, residue 8144. -/
theorem bounds_13_8144 : exactInterval 13 8144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8144 : oddCount 8144 13 = 7 ∧ acceleratedOrbit 13 8144 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8144) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8144.1, data_13_8144.2]

end Collatz.Research.StoppingAtlas.Batch0997
