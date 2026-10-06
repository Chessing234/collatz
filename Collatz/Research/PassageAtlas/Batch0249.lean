import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0249

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8126. -/
theorem bounds_15_8126 : exactInterval 15 8126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8126 : oddCount 8126 15 = 8 ∧ acceleratedOrbit 15 8126 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8126) = 3 ^ 8 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8126.1, data_15_8126.2]

/-- Complete interval computation for depth 15, residue 8127. -/
theorem bounds_15_8127 : exactInterval 15 8127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8127 : oddCount 8127 15 = 11 ∧ acceleratedOrbit 15 8127 = 43942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8127) = 3 ^ 11 * m + 43942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8127.1, data_15_8127.2]

/-- Complete interval computation for depth 15, residue 8128. -/
theorem bounds_15_8128 : exactInterval 15 8128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8128 : oddCount 8128 15 = 8 ∧ acceleratedOrbit 15 8128 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8128) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8128.1, data_15_8128.2]

/-- Complete interval computation for depth 15, residue 8129. -/
theorem bounds_15_8129 : exactInterval 15 8129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8129 : oddCount 8129 15 = 6 ∧ acceleratedOrbit 15 8129 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8129) = 3 ^ 6 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8129.1, data_15_8129.2]

/-- Complete interval computation for depth 15, residue 8130. -/
theorem bounds_15_8130 : exactInterval 15 8130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8130 : oddCount 8130 15 = 11 ∧ acceleratedOrbit 15 8130 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8130) = 3 ^ 11 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8130.1, data_15_8130.2]

/-- Complete interval computation for depth 15, residue 8131. -/
theorem bounds_15_8131 : exactInterval 15 8131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8131 : oddCount 8131 15 = 11 ∧ acceleratedOrbit 15 8131 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8131) = 3 ^ 11 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8131.1, data_15_8131.2]

/-- Complete interval computation for depth 15, residue 8132. -/
theorem bounds_15_8132 : exactInterval 15 8132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8132 : oddCount 8132 15 = 6 ∧ acceleratedOrbit 15 8132 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8132) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8132.1, data_15_8132.2]

/-- Complete interval computation for depth 15, residue 8133. -/
theorem bounds_15_8133 : exactInterval 15 8133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8133 : oddCount 8133 15 = 6 ∧ acceleratedOrbit 15 8133 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8133) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8133.1, data_15_8133.2]

/-- Complete interval computation for depth 15, residue 8134. -/
theorem bounds_15_8134 : exactInterval 15 8134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8134 : oddCount 8134 15 = 6 ∧ acceleratedOrbit 15 8134 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8134) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8134.1, data_15_8134.2]

/-- Complete interval computation for depth 15, residue 8135. -/
theorem bounds_15_8135 : exactInterval 15 8135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8135 : oddCount 8135 15 = 9 ∧ acceleratedOrbit 15 8135 = 4888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8135) = 3 ^ 9 * m + 4888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8135.1, data_15_8135.2]

/-- Complete interval computation for depth 15, residue 8136. -/
theorem bounds_15_8136 : exactInterval 15 8136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8136 : oddCount 8136 15 = 8 ∧ acceleratedOrbit 15 8136 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8136) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8136.1, data_15_8136.2]

/-- Complete interval computation for depth 15, residue 8137. -/
theorem bounds_15_8137 : exactInterval 15 8137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8137 : oddCount 8137 15 = 8 ∧ acceleratedOrbit 15 8137 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8137) = 3 ^ 8 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8137.1, data_15_8137.2]

/-- Complete interval computation for depth 15, residue 8138. -/
theorem bounds_15_8138 : exactInterval 15 8138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8138 : oddCount 8138 15 = 8 ∧ acceleratedOrbit 15 8138 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8138) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8138.1, data_15_8138.2]

/-- Complete interval computation for depth 15, residue 8139. -/
theorem bounds_15_8139 : exactInterval 15 8139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8139 : oddCount 8139 15 = 6 ∧ acceleratedOrbit 15 8139 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8139) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8139.1, data_15_8139.2]

/-- Complete interval computation for depth 15, residue 8140. -/
theorem bounds_15_8140 : exactInterval 15 8140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8140 : oddCount 8140 15 = 8 ∧ acceleratedOrbit 15 8140 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8140) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8140.1, data_15_8140.2]

/-- Complete interval computation for depth 15, residue 8141. -/
theorem bounds_15_8141 : exactInterval 15 8141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8141 : oddCount 8141 15 = 8 ∧ acceleratedOrbit 15 8141 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8141) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8141.1, data_15_8141.2]

/-- Complete interval computation for depth 15, residue 8142. -/
theorem bounds_15_8142 : exactInterval 15 8142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8142 : oddCount 8142 15 = 8 ∧ acceleratedOrbit 15 8142 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8142) = 3 ^ 8 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8142.1, data_15_8142.2]

/-- Complete interval computation for depth 15, residue 8143. -/
theorem bounds_15_8143 : exactInterval 15 8143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8143 : oddCount 8143 15 = 8 ∧ acceleratedOrbit 15 8143 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8143) = 3 ^ 8 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8143.1, data_15_8143.2]

/-- Complete interval computation for depth 15, residue 8144. -/
theorem bounds_15_8144 : exactInterval 15 8144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8144 : oddCount 8144 15 = 8 ∧ acceleratedOrbit 15 8144 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8144) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8144.1, data_15_8144.2]

/-- Complete interval computation for depth 15, residue 8145. -/
theorem bounds_15_8145 : exactInterval 15 8145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8145 : oddCount 8145 15 = 8 ∧ acceleratedOrbit 15 8145 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8145) = 3 ^ 8 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8145.1, data_15_8145.2]

/-- Complete interval computation for depth 15, residue 8146. -/
theorem bounds_15_8146 : exactInterval 15 8146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8146 : oddCount 8146 15 = 10 ∧ acceleratedOrbit 15 8146 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8146) = 3 ^ 10 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8146.1, data_15_8146.2]

/-- Complete interval computation for depth 15, residue 8147. -/
theorem bounds_15_8147 : exactInterval 15 8147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8147 : oddCount 8147 15 = 10 ∧ acceleratedOrbit 15 8147 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8147) = 3 ^ 10 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8147.1, data_15_8147.2]

/-- Complete interval computation for depth 15, residue 8148. -/
theorem bounds_15_8148 : exactInterval 15 8148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8148 : oddCount 8148 15 = 8 ∧ acceleratedOrbit 15 8148 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8148) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8148.1, data_15_8148.2]

/-- Complete interval computation for depth 15, residue 8149. -/
theorem bounds_15_8149 : exactInterval 15 8149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8149 : oddCount 8149 15 = 8 ∧ acceleratedOrbit 15 8149 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8149) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8149.1, data_15_8149.2]

/-- Complete interval computation for depth 15, residue 8150. -/
theorem bounds_15_8150 : exactInterval 15 8150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8150 : oddCount 8150 15 = 9 ∧ acceleratedOrbit 15 8150 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8150) = 3 ^ 9 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8150.1, data_15_8150.2]

/-- Complete interval computation for depth 15, residue 8151. -/
theorem bounds_15_8151 : exactInterval 15 8151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8151 : oddCount 8151 15 = 9 ∧ acceleratedOrbit 15 8151 = 4898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8151) = 3 ^ 9 * m + 4898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8151.1, data_15_8151.2]

/-- Complete interval computation for depth 15, residue 8152. -/
theorem bounds_15_8152 : exactInterval 15 8152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8152 : oddCount 8152 15 = 7 ∧ acceleratedOrbit 15 8152 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8152) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8152.1, data_15_8152.2]

/-- Complete interval computation for depth 15, residue 8153. -/
theorem bounds_15_8153 : exactInterval 15 8153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8153 : oddCount 8153 15 = 6 ∧ acceleratedOrbit 15 8153 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8153) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8153.1, data_15_8153.2]

/-- Complete interval computation for depth 15, residue 8154. -/
theorem bounds_15_8154 : exactInterval 15 8154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8154 : oddCount 8154 15 = 7 ∧ acceleratedOrbit 15 8154 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8154) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8154.1, data_15_8154.2]

/-- Complete interval computation for depth 15, residue 8155. -/
theorem bounds_15_8155 : exactInterval 15 8155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8155 : oddCount 8155 15 = 10 ∧ acceleratedOrbit 15 8155 = 14701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8155) = 3 ^ 10 * m + 14701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8155.1, data_15_8155.2]

/-- Complete interval computation for depth 15, residue 8156. -/
theorem bounds_15_8156 : exactInterval 15 8156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8156 : oddCount 8156 15 = 7 ∧ acceleratedOrbit 15 8156 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8156) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8156.1, data_15_8156.2]

/-- Complete interval computation for depth 15, residue 8157. -/
theorem bounds_15_8157 : exactInterval 15 8157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8157 : oddCount 8157 15 = 7 ∧ acceleratedOrbit 15 8157 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8157) = 3 ^ 7 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8157.1, data_15_8157.2]

/-- Complete interval computation for depth 15, residue 8158. -/
theorem bounds_15_8158 : exactInterval 15 8158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8158 : oddCount 8158 15 = 8 ∧ acceleratedOrbit 15 8158 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8158) = 3 ^ 8 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8158.1, data_15_8158.2]

end Collatz.Research.PassageAtlas.Batch0249
