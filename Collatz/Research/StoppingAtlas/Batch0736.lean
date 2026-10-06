import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0736

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4121. -/
theorem bounds_13_4121 : exactInterval 13 4121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4121 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4121) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4121 : oddCount 4121 13 = 6 ∧ acceleratedOrbit 13 4121 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4121 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4121) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4121.1, data_13_4121.2]

/-- Complete interval computation for depth 13, residue 4122. -/
theorem bounds_13_4122 : exactInterval 13 4122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4122 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4122) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4122 : oddCount 4122 13 = 4 ∧ acceleratedOrbit 13 4122 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4122 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4122) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4122.1, data_13_4122.2]

/-- Complete interval computation for depth 13, residue 4123. -/
theorem bounds_13_4123 : exactInterval 13 4123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4123 : oddCount 4123 13 = 9 ∧ acceleratedOrbit 13 4123 = 9910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4123) = 3 ^ 9 * m + 9910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4123.1, data_13_4123.2]

/-- Complete interval computation for depth 13, residue 4124. -/
theorem bounds_13_4124 : exactInterval 13 4124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4124 : oddCount 4124 13 = 6 ∧ acceleratedOrbit 13 4124 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4124) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4124.1, data_13_4124.2]

/-- Complete interval computation for depth 13, residue 4125. -/
theorem bounds_13_4125 : exactInterval 13 4125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4125 : oddCount 4125 13 = 6 ∧ acceleratedOrbit 13 4125 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4125) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4125.1, data_13_4125.2]

/-- Complete interval computation for depth 13, residue 4126. -/
theorem bounds_13_4126 : exactInterval 13 4126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4126 : oddCount 4126 13 = 6 ∧ acceleratedOrbit 13 4126 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4126) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4126.1, data_13_4126.2]

/-- Complete interval computation for depth 13, residue 4127. -/
theorem bounds_13_4127 : exactInterval 13 4127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4127 : oddCount 4127 13 = 9 ∧ acceleratedOrbit 13 4127 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4127) = 3 ^ 9 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4127.1, data_13_4127.2]

/-- Complete interval computation for depth 13, residue 4128. -/
theorem bounds_13_4128 : exactInterval 13 4128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4128 : oddCount 4128 13 = 5 ∧ acceleratedOrbit 13 4128 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4128) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4128.1, data_13_4128.2]

/-- Complete interval computation for depth 13, residue 4129. -/
theorem bounds_13_4129 : exactInterval 13 4129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4129 : oddCount 4129 13 = 8 ∧ acceleratedOrbit 13 4129 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4129) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4129.1, data_13_4129.2]

/-- Complete interval computation for depth 13, residue 4130. -/
theorem bounds_13_4130 : exactInterval 13 4130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4130 : oddCount 4130 13 = 4 ∧ acceleratedOrbit 13 4130 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4130) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4130.1, data_13_4130.2]

/-- Complete interval computation for depth 13, residue 4131. -/
theorem bounds_13_4131 : exactInterval 13 4131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4131 : oddCount 4131 13 = 4 ∧ acceleratedOrbit 13 4131 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4131) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4131.1, data_13_4131.2]

/-- Complete interval computation for depth 13, residue 4132. -/
theorem bounds_13_4132 : exactInterval 13 4132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4132 : oddCount 4132 13 = 7 ∧ acceleratedOrbit 13 4132 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4132) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4132.1, data_13_4132.2]

/-- Complete interval computation for depth 13, residue 4133. -/
theorem bounds_13_4133 : exactInterval 13 4133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4133 : oddCount 4133 13 = 7 ∧ acceleratedOrbit 13 4133 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4133) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4133.1, data_13_4133.2]

/-- Complete interval computation for depth 13, residue 4134. -/
theorem bounds_13_4134 : exactInterval 13 4134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4134 : oddCount 4134 13 = 7 ∧ acceleratedOrbit 13 4134 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4134) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4134.1, data_13_4134.2]

/-- Complete interval computation for depth 13, residue 4135. -/
theorem bounds_13_4135 : exactInterval 13 4135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4135 : oddCount 4135 13 = 8 ∧ acceleratedOrbit 13 4135 = 3314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4135) = 3 ^ 8 * m + 3314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4135.1, data_13_4135.2]

end Collatz.Research.StoppingAtlas.Batch0736
