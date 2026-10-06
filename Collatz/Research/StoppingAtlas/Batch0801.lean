import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0801

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5120. -/
theorem bounds_13_5120 : exactInterval 13 5120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5120 : oddCount 5120 13 = 1 ∧ acceleratedOrbit 13 5120 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5120) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5120.1, data_13_5120.2]

/-- Complete interval computation for depth 13, residue 5121. -/
theorem bounds_13_5121 : exactInterval 13 5121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5121 : oddCount 5121 13 = 5 ∧ acceleratedOrbit 13 5121 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5121) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5121.1, data_13_5121.2]

/-- Complete interval computation for depth 13, residue 5122. -/
theorem bounds_13_5122 : exactInterval 13 5122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5122 : oddCount 5122 13 = 7 ∧ acceleratedOrbit 13 5122 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5122) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5122.1, data_13_5122.2]

/-- Complete interval computation for depth 13, residue 5123. -/
theorem bounds_13_5123 : exactInterval 13 5123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5123 : oddCount 5123 13 = 7 ∧ acceleratedOrbit 13 5123 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5123) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5123.1, data_13_5123.2]

/-- Complete interval computation for depth 13, residue 5124. -/
theorem bounds_13_5124 : exactInterval 13 5124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5124 : oddCount 5124 13 = 6 ∧ acceleratedOrbit 13 5124 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5124) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5124.1, data_13_5124.2]

/-- Complete interval computation for depth 13, residue 5125. -/
theorem bounds_13_5125 : exactInterval 13 5125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5125 : oddCount 5125 13 = 6 ∧ acceleratedOrbit 13 5125 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5125) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5125.1, data_13_5125.2]

/-- Complete interval computation for depth 13, residue 5126. -/
theorem bounds_13_5126 : exactInterval 13 5126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5126 : oddCount 5126 13 = 6 ∧ acceleratedOrbit 13 5126 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5126) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5126.1, data_13_5126.2]

/-- Complete interval computation for depth 13, residue 5127. -/
theorem bounds_13_5127 : exactInterval 13 5127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5127 : oddCount 5127 13 = 7 ∧ acceleratedOrbit 13 5127 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5127) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5127.1, data_13_5127.2]

/-- Complete interval computation for depth 13, residue 5128. -/
theorem bounds_13_5128 : exactInterval 13 5128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5128 : oddCount 5128 13 = 7 ∧ acceleratedOrbit 13 5128 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5128) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5128.1, data_13_5128.2]

/-- Complete interval computation for depth 13, residue 5129. -/
theorem bounds_13_5129 : exactInterval 13 5129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5129 : oddCount 5129 13 = 7 ∧ acceleratedOrbit 13 5129 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5129) = 3 ^ 7 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5129.1, data_13_5129.2]

/-- Complete interval computation for depth 13, residue 5130. -/
theorem bounds_13_5130 : exactInterval 13 5130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5130 : oddCount 5130 13 = 7 ∧ acceleratedOrbit 13 5130 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5130) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5130.1, data_13_5130.2]

/-- Complete interval computation for depth 13, residue 5131. -/
theorem bounds_13_5131 : exactInterval 13 5131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5131 : oddCount 5131 13 = 6 ∧ acceleratedOrbit 13 5131 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5131) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5131.1, data_13_5131.2]

/-- Complete interval computation for depth 13, residue 5132. -/
theorem bounds_13_5132 : exactInterval 13 5132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5132 : oddCount 5132 13 = 7 ∧ acceleratedOrbit 13 5132 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5132) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5132.1, data_13_5132.2]

/-- Complete interval computation for depth 13, residue 5133. -/
theorem bounds_13_5133 : exactInterval 13 5133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5133 : oddCount 5133 13 = 7 ∧ acceleratedOrbit 13 5133 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5133) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5133.1, data_13_5133.2]

/-- Complete interval computation for depth 13, residue 5134. -/
theorem bounds_13_5134 : exactInterval 13 5134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5134 : oddCount 5134 13 = 7 ∧ acceleratedOrbit 13 5134 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5134) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5134.1, data_13_5134.2]

end Collatz.Research.StoppingAtlas.Batch0801
