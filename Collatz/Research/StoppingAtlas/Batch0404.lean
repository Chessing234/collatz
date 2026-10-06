import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0404

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3118. -/
theorem bounds_12_3118 : exactInterval 12 3118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3118 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3118) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3118 : oddCount 3118 12 = 6 ∧ acceleratedOrbit 12 3118 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3118 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3118) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3118.1, data_12_3118.2]

/-- Complete interval computation for depth 12, residue 3119. -/
theorem bounds_12_3119 : exactInterval 12 3119 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3119 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3119) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3119 : oddCount 3119 12 = 7 ∧ acceleratedOrbit 12 3119 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3119 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3119) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3119.1, data_12_3119.2]

/-- Complete interval computation for depth 12, residue 3120. -/
theorem bounds_12_3120 : exactInterval 12 3120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3120 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3120) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3120 : oddCount 3120 12 = 5 ∧ acceleratedOrbit 12 3120 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3120 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3120) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3120.1, data_12_3120.2]

/-- Complete interval computation for depth 12, residue 3121. -/
theorem bounds_12_3121 : exactInterval 12 3121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3121 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3121) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3121 : oddCount 3121 12 = 6 ∧ acceleratedOrbit 12 3121 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3121 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3121) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3121.1, data_12_3121.2]

/-- Complete interval computation for depth 12, residue 3122. -/
theorem bounds_12_3122 : exactInterval 12 3122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3122 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3122) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3122 : oddCount 3122 12 = 6 ∧ acceleratedOrbit 12 3122 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3122 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3122) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3122.1, data_12_3122.2]

/-- Complete interval computation for depth 12, residue 3123. -/
theorem bounds_12_3123 : exactInterval 12 3123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3123 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3123) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3123 : oddCount 3123 12 = 6 ∧ acceleratedOrbit 12 3123 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3123 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3123) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3123.1, data_12_3123.2]

/-- Complete interval computation for depth 12, residue 3124. -/
theorem bounds_12_3124 : exactInterval 12 3124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3124 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3124) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3124 : oddCount 3124 12 = 5 ∧ acceleratedOrbit 12 3124 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3124 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3124) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3124.1, data_12_3124.2]

/-- Complete interval computation for depth 12, residue 3125. -/
theorem bounds_12_3125 : exactInterval 12 3125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3125 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3125) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3125 : oddCount 3125 12 = 5 ∧ acceleratedOrbit 12 3125 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3125 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3125) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3125.1, data_12_3125.2]

/-- Complete interval computation for depth 12, residue 3126. -/
theorem bounds_12_3126 : exactInterval 12 3126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3126 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3126) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3126 : oddCount 3126 12 = 8 ∧ acceleratedOrbit 12 3126 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3126 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3126) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3126.1, data_12_3126.2]

/-- Complete interval computation for depth 12, residue 3127. -/
theorem bounds_12_3127 : exactInterval 12 3127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3127 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3127) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3127 : oddCount 3127 12 = 8 ∧ acceleratedOrbit 12 3127 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3127 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3127) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3127.1, data_12_3127.2]

/-- Complete interval computation for depth 12, residue 3128. -/
theorem bounds_12_3128 : exactInterval 12 3128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3128 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3128) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3128 : oddCount 3128 12 = 4 ∧ acceleratedOrbit 12 3128 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3128 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3128) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3128.1, data_12_3128.2]

/-- Complete interval computation for depth 12, residue 3129. -/
theorem bounds_12_3129 : exactInterval 12 3129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3129 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3129) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3129 : oddCount 3129 12 = 7 ∧ acceleratedOrbit 12 3129 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3129 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3129) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3129.1, data_12_3129.2]

/-- Complete interval computation for depth 12, residue 3130. -/
theorem bounds_12_3130 : exactInterval 12 3130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3130 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3130) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3130 : oddCount 3130 12 = 4 ∧ acceleratedOrbit 12 3130 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3130 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3130) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3130.1, data_12_3130.2]

/-- Complete interval computation for depth 12, residue 3131. -/
theorem bounds_12_3131 : exactInterval 12 3131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3131 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3131) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3131 : oddCount 3131 12 = 8 ∧ acceleratedOrbit 12 3131 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3131 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3131) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3131.1, data_12_3131.2]

/-- Complete interval computation for depth 12, residue 3132. -/
theorem bounds_12_3132 : exactInterval 12 3132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3132 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3132) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3132 : oddCount 3132 12 = 4 ∧ acceleratedOrbit 12 3132 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3132 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3132) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3132.1, data_12_3132.2]

end Collatz.Research.StoppingAtlas.Batch0404
