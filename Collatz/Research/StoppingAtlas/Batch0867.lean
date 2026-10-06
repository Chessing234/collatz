import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0867

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6133. -/
theorem bounds_13_6133 : exactInterval 13 6133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6133 : oddCount 6133 13 = 7 ∧ acceleratedOrbit 13 6133 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6133) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6133.1, data_13_6133.2]

/-- Complete interval computation for depth 13, residue 6134. -/
theorem bounds_13_6134 : exactInterval 13 6134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6134 : oddCount 6134 13 = 8 ∧ acceleratedOrbit 13 6134 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6134) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6134.1, data_13_6134.2]

/-- Complete interval computation for depth 13, residue 6135. -/
theorem bounds_13_6135 : exactInterval 13 6135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6135 : oddCount 6135 13 = 8 ∧ acceleratedOrbit 13 6135 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6135) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6135.1, data_13_6135.2]

/-- Complete interval computation for depth 13, residue 6136. -/
theorem bounds_13_6136 : exactInterval 13 6136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6136 : oddCount 6136 13 = 9 ∧ acceleratedOrbit 13 6136 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6136) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6136.1, data_13_6136.2]

/-- Complete interval computation for depth 13, residue 6137. -/
theorem bounds_13_6137 : exactInterval 13 6137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6137 : oddCount 6137 13 = 7 ∧ acceleratedOrbit 13 6137 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6137) = 3 ^ 7 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6137.1, data_13_6137.2]

/-- Complete interval computation for depth 13, residue 6138. -/
theorem bounds_13_6138 : exactInterval 13 6138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6138 : oddCount 6138 13 = 9 ∧ acceleratedOrbit 13 6138 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6138) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6138.1, data_13_6138.2]

/-- Complete interval computation for depth 13, residue 6139. -/
theorem bounds_13_6139 : exactInterval 13 6139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6139 : oddCount 6139 13 = 9 ∧ acceleratedOrbit 13 6139 = 14755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6139) = 3 ^ 9 * m + 14755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6139.1, data_13_6139.2]

/-- Complete interval computation for depth 13, residue 6140. -/
theorem bounds_13_6140 : exactInterval 13 6140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6140 : oddCount 6140 13 = 9 ∧ acceleratedOrbit 13 6140 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6140) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6140.1, data_13_6140.2]

/-- Complete interval computation for depth 13, residue 6141. -/
theorem bounds_13_6141 : exactInterval 13 6141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6141 : oddCount 6141 13 = 9 ∧ acceleratedOrbit 13 6141 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6141) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6141.1, data_13_6141.2]

/-- Complete interval computation for depth 13, residue 6142. -/
theorem bounds_13_6142 : exactInterval 13 6142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6142 : oddCount 6142 13 = 11 ∧ acceleratedOrbit 13 6142 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6142) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6142.1, data_13_6142.2]

/-- Complete interval computation for depth 13, residue 6143. -/
theorem bounds_13_6143 : exactInterval 13 6143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6143 : oddCount 6143 13 = 11 ∧ acceleratedOrbit 13 6143 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6143) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6143.1, data_13_6143.2]

/-- Complete interval computation for depth 13, residue 6144. -/
theorem bounds_13_6144 : exactInterval 13 6144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6144 : oddCount 6144 13 = 2 ∧ acceleratedOrbit 13 6144 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6144) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6144.1, data_13_6144.2]

/-- Complete interval computation for depth 13, residue 6145. -/
theorem bounds_13_6145 : exactInterval 13 6145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6145 : oddCount 6145 13 = 7 ∧ acceleratedOrbit 13 6145 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6145) = 3 ^ 7 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6145.1, data_13_6145.2]

/-- Complete interval computation for depth 13, residue 6146. -/
theorem bounds_13_6146 : exactInterval 13 6146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6146 : oddCount 6146 13 = 6 ∧ acceleratedOrbit 13 6146 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6146) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6146.1, data_13_6146.2]

/-- Complete interval computation for depth 13, residue 6147. -/
theorem bounds_13_6147 : exactInterval 13 6147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6147 : oddCount 6147 13 = 6 ∧ acceleratedOrbit 13 6147 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6147) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6147.1, data_13_6147.2]

/-- Complete interval computation for depth 13, residue 6148. -/
theorem bounds_13_6148 : exactInterval 13 6148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6148 : oddCount 6148 13 = 7 ∧ acceleratedOrbit 13 6148 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6148) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6148.1, data_13_6148.2]

end Collatz.Research.StoppingAtlas.Batch0867
