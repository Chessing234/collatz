import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0996

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8115. -/
theorem bounds_13_8115 : exactInterval 13 8115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8115 : oddCount 8115 13 = 5 ∧ acceleratedOrbit 13 8115 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8115) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8115.1, data_13_8115.2]

/-- Complete interval computation for depth 13, residue 8116. -/
theorem bounds_13_8116 : exactInterval 13 8116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8116 : oddCount 8116 13 = 6 ∧ acceleratedOrbit 13 8116 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8116) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8116.1, data_13_8116.2]

/-- Complete interval computation for depth 13, residue 8117. -/
theorem bounds_13_8117 : exactInterval 13 8117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8117 : oddCount 8117 13 = 6 ∧ acceleratedOrbit 13 8117 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8117) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8117.1, data_13_8117.2]

/-- Complete interval computation for depth 13, residue 8118. -/
theorem bounds_13_8118 : exactInterval 13 8118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8118 : oddCount 8118 13 = 8 ∧ acceleratedOrbit 13 8118 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8118) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8118.1, data_13_8118.2]

/-- Complete interval computation for depth 13, residue 8119. -/
theorem bounds_13_8119 : exactInterval 13 8119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8119 : oddCount 8119 13 = 8 ∧ acceleratedOrbit 13 8119 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8119) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8119.1, data_13_8119.2]

/-- Complete interval computation for depth 13, residue 8120. -/
theorem bounds_13_8120 : exactInterval 13 8120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8120 : oddCount 8120 13 = 6 ∧ acceleratedOrbit 13 8120 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8120) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8120.1, data_13_8120.2]

/-- Complete interval computation for depth 13, residue 8121. -/
theorem bounds_13_8121 : exactInterval 13 8121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8121 : oddCount 8121 13 = 5 ∧ acceleratedOrbit 13 8121 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8121) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8121.1, data_13_8121.2]

/-- Complete interval computation for depth 13, residue 8122. -/
theorem bounds_13_8122 : exactInterval 13 8122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8122 : oddCount 8122 13 = 6 ∧ acceleratedOrbit 13 8122 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8122) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8122.1, data_13_8122.2]

/-- Complete interval computation for depth 13, residue 8123. -/
theorem bounds_13_8123 : exactInterval 13 8123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8123 : oddCount 8123 13 = 5 ∧ acceleratedOrbit 13 8123 = 241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8123) = 3 ^ 5 * m + 241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8123.1, data_13_8123.2]

/-- Complete interval computation for depth 13, residue 8124. -/
theorem bounds_13_8124 : exactInterval 13 8124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8124 : oddCount 8124 13 = 7 ∧ acceleratedOrbit 13 8124 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8124) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8124.1, data_13_8124.2]

/-- Complete interval computation for depth 13, residue 8125. -/
theorem bounds_13_8125 : exactInterval 13 8125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8125 : oddCount 8125 13 = 7 ∧ acceleratedOrbit 13 8125 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8125) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8125.1, data_13_8125.2]

/-- Complete interval computation for depth 13, residue 8126. -/
theorem bounds_13_8126 : exactInterval 13 8126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8126 : oddCount 8126 13 = 7 ∧ acceleratedOrbit 13 8126 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8126) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8126.1, data_13_8126.2]

/-- Complete interval computation for depth 13, residue 8127. -/
theorem bounds_13_8127 : exactInterval 13 8127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8127 : oddCount 8127 13 = 10 ∧ acceleratedOrbit 13 8127 = 58589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8127) = 3 ^ 10 * m + 58589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8127.1, data_13_8127.2]

/-- Complete interval computation for depth 13, residue 8128. -/
theorem bounds_13_8128 : exactInterval 13 8128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8128 : oddCount 8128 13 = 7 ∧ acceleratedOrbit 13 8128 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8128) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8128.1, data_13_8128.2]

/-- Complete interval computation for depth 13, residue 8129. -/
theorem bounds_13_8129 : exactInterval 13 8129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8129 : oddCount 8129 13 = 6 ∧ acceleratedOrbit 13 8129 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8129) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8129.1, data_13_8129.2]

end Collatz.Research.StoppingAtlas.Batch0996
