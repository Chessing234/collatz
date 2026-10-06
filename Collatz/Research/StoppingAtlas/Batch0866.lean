import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0866

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6118. -/
theorem bounds_13_6118 : exactInterval 13 6118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6118 : oddCount 6118 13 = 6 ∧ acceleratedOrbit 13 6118 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6118) = 3 ^ 6 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6118.1, data_13_6118.2]

/-- Complete interval computation for depth 13, residue 6119. -/
theorem bounds_13_6119 : exactInterval 13 6119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6119 : oddCount 6119 13 = 7 ∧ acceleratedOrbit 13 6119 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6119) = 3 ^ 7 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6119.1, data_13_6119.2]

/-- Complete interval computation for depth 13, residue 6120. -/
theorem bounds_13_6120 : exactInterval 13 6120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6120 : oddCount 6120 13 = 7 ∧ acceleratedOrbit 13 6120 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6120) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6120.1, data_13_6120.2]

/-- Complete interval computation for depth 13, residue 6121. -/
theorem bounds_13_6121 : exactInterval 13 6121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6121 : oddCount 6121 13 = 10 ∧ acceleratedOrbit 13 6121 = 44135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6121) = 3 ^ 10 * m + 44135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6121.1, data_13_6121.2]

/-- Complete interval computation for depth 13, residue 6122. -/
theorem bounds_13_6122 : exactInterval 13 6122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6122 : oddCount 6122 13 = 7 ∧ acceleratedOrbit 13 6122 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6122) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6122.1, data_13_6122.2]

/-- Complete interval computation for depth 13, residue 6123. -/
theorem bounds_13_6123 : exactInterval 13 6123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6123 : oddCount 6123 13 = 9 ∧ acceleratedOrbit 13 6123 = 14717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6123) = 3 ^ 9 * m + 14717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6123.1, data_13_6123.2]

/-- Complete interval computation for depth 13, residue 6124. -/
theorem bounds_13_6124 : exactInterval 13 6124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6124 : oddCount 6124 13 = 7 ∧ acceleratedOrbit 13 6124 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6124) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6124.1, data_13_6124.2]

/-- Complete interval computation for depth 13, residue 6125. -/
theorem bounds_13_6125 : exactInterval 13 6125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6125 : oddCount 6125 13 = 7 ∧ acceleratedOrbit 13 6125 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6125) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6125.1, data_13_6125.2]

/-- Complete interval computation for depth 13, residue 6126. -/
theorem bounds_13_6126 : exactInterval 13 6126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6126 : oddCount 6126 13 = 7 ∧ acceleratedOrbit 13 6126 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6126) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6126.1, data_13_6126.2]

/-- Complete interval computation for depth 13, residue 6127. -/
theorem bounds_13_6127 : exactInterval 13 6127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6127 : oddCount 6127 13 = 7 ∧ acceleratedOrbit 13 6127 = 1636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6127) = 3 ^ 7 * m + 1636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6127.1, data_13_6127.2]

/-- Complete interval computation for depth 13, residue 6128. -/
theorem bounds_13_6128 : exactInterval 13 6128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6128 : oddCount 6128 13 = 7 ∧ acceleratedOrbit 13 6128 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6128) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6128.1, data_13_6128.2]

/-- Complete interval computation for depth 13, residue 6129. -/
theorem bounds_13_6129 : exactInterval 13 6129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6129 : oddCount 6129 13 = 7 ∧ acceleratedOrbit 13 6129 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6129) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6129.1, data_13_6129.2]

/-- Complete interval computation for depth 13, residue 6130. -/
theorem bounds_13_6130 : exactInterval 13 6130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6130 : oddCount 6130 13 = 9 ∧ acceleratedOrbit 13 6130 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6130) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6130.1, data_13_6130.2]

/-- Complete interval computation for depth 13, residue 6131. -/
theorem bounds_13_6131 : exactInterval 13 6131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6131 : oddCount 6131 13 = 9 ∧ acceleratedOrbit 13 6131 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6131) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6131.1, data_13_6131.2]

/-- Complete interval computation for depth 13, residue 6132. -/
theorem bounds_13_6132 : exactInterval 13 6132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6132 : oddCount 6132 13 = 7 ∧ acceleratedOrbit 13 6132 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6132) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6132.1, data_13_6132.2]

end Collatz.Research.StoppingAtlas.Batch0866
