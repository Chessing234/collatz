import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0802

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5135. -/
theorem bounds_13_5135 : exactInterval 13 5135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5135 : oddCount 5135 13 = 7 ∧ acceleratedOrbit 13 5135 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5135) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5135.1, data_13_5135.2]

/-- Complete interval computation for depth 13, residue 5136. -/
theorem bounds_13_5136 : exactInterval 13 5136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5136 : oddCount 5136 13 = 3 ∧ acceleratedOrbit 13 5136 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5136) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5136.1, data_13_5136.2]

/-- Complete interval computation for depth 13, residue 5137. -/
theorem bounds_13_5137 : exactInterval 13 5137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5137 : oddCount 5137 13 = 7 ∧ acceleratedOrbit 13 5137 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5137) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5137.1, data_13_5137.2]

/-- Complete interval computation for depth 13, residue 5138. -/
theorem bounds_13_5138 : exactInterval 13 5138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5138 : oddCount 5138 13 = 6 ∧ acceleratedOrbit 13 5138 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5138) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5138.1, data_13_5138.2]

/-- Complete interval computation for depth 13, residue 5139. -/
theorem bounds_13_5139 : exactInterval 13 5139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5139 : oddCount 5139 13 = 6 ∧ acceleratedOrbit 13 5139 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5139) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5139.1, data_13_5139.2]

/-- Complete interval computation for depth 13, residue 5140. -/
theorem bounds_13_5140 : exactInterval 13 5140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5140 : oddCount 5140 13 = 3 ∧ acceleratedOrbit 13 5140 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5140) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5140.1, data_13_5140.2]

/-- Complete interval computation for depth 13, residue 5141. -/
theorem bounds_13_5141 : exactInterval 13 5141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5141 : oddCount 5141 13 = 3 ∧ acceleratedOrbit 13 5141 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5141) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5141.1, data_13_5141.2]

/-- Complete interval computation for depth 13, residue 5142. -/
theorem bounds_13_5142 : exactInterval 13 5142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5142 : oddCount 5142 13 = 7 ∧ acceleratedOrbit 13 5142 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5142) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5142.1, data_13_5142.2]

/-- Complete interval computation for depth 13, residue 5143. -/
theorem bounds_13_5143 : exactInterval 13 5143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5143 : oddCount 5143 13 = 7 ∧ acceleratedOrbit 13 5143 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5143) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5143.1, data_13_5143.2]

/-- Complete interval computation for depth 13, residue 5144. -/
theorem bounds_13_5144 : exactInterval 13 5144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5144 : oddCount 5144 13 = 3 ∧ acceleratedOrbit 13 5144 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5144) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5144.1, data_13_5144.2]

/-- Complete interval computation for depth 13, residue 5145. -/
theorem bounds_13_5145 : exactInterval 13 5145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5145 : oddCount 5145 13 = 8 ∧ acceleratedOrbit 13 5145 = 4124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5145) = 3 ^ 8 * m + 4124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5145.1, data_13_5145.2]

/-- Complete interval computation for depth 13, residue 5146. -/
theorem bounds_13_5146 : exactInterval 13 5146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5146 : oddCount 5146 13 = 3 ∧ acceleratedOrbit 13 5146 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5146) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5146.1, data_13_5146.2]

/-- Complete interval computation for depth 13, residue 5147. -/
theorem bounds_13_5147 : exactInterval 13 5147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5147 : oddCount 5147 13 = 10 ∧ acceleratedOrbit 13 5147 = 37111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5147) = 3 ^ 10 * m + 37111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5147.1, data_13_5147.2]

/-- Complete interval computation for depth 13, residue 5148. -/
theorem bounds_13_5148 : exactInterval 13 5148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5148 : oddCount 5148 13 = 8 ∧ acceleratedOrbit 13 5148 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5148) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5148.1, data_13_5148.2]

/-- Complete interval computation for depth 13, residue 5149. -/
theorem bounds_13_5149 : exactInterval 13 5149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5149 : oddCount 5149 13 = 8 ∧ acceleratedOrbit 13 5149 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5149) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5149.1, data_13_5149.2]

end Collatz.Research.StoppingAtlas.Batch0802
