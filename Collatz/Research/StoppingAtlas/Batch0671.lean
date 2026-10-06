import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0671

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3123. -/
theorem bounds_13_3123 : exactInterval 13 3123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3123 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3123) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3123 : oddCount 3123 13 = 7 ∧ acceleratedOrbit 13 3123 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3123 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3123) = 3 ^ 7 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3123.1, data_13_3123.2]

/-- Complete interval computation for depth 13, residue 3124. -/
theorem bounds_13_3124 : exactInterval 13 3124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3124 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3124) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3124 : oddCount 3124 13 = 5 ∧ acceleratedOrbit 13 3124 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3124 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3124) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3124.1, data_13_3124.2]

/-- Complete interval computation for depth 13, residue 3125. -/
theorem bounds_13_3125 : exactInterval 13 3125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3125 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3125) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3125 : oddCount 3125 13 = 5 ∧ acceleratedOrbit 13 3125 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3125 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3125) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3125.1, data_13_3125.2]

/-- Complete interval computation for depth 13, residue 3126. -/
theorem bounds_13_3126 : exactInterval 13 3126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3126 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3126) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3126 : oddCount 3126 13 = 8 ∧ acceleratedOrbit 13 3126 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3126 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3126) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3126.1, data_13_3126.2]

/-- Complete interval computation for depth 13, residue 3127. -/
theorem bounds_13_3127 : exactInterval 13 3127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3127 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3127) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3127 : oddCount 3127 13 = 8 ∧ acceleratedOrbit 13 3127 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3127 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3127) = 3 ^ 8 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3127.1, data_13_3127.2]

/-- Complete interval computation for depth 13, residue 3128. -/
theorem bounds_13_3128 : exactInterval 13 3128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3128 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3128) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3128 : oddCount 3128 13 = 4 ∧ acceleratedOrbit 13 3128 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3128 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3128) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3128.1, data_13_3128.2]

/-- Complete interval computation for depth 13, residue 3129. -/
theorem bounds_13_3129 : exactInterval 13 3129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3129 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3129) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3129 : oddCount 3129 13 = 8 ∧ acceleratedOrbit 13 3129 = 2510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3129 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3129) = 3 ^ 8 * m + 2510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3129.1, data_13_3129.2]

/-- Complete interval computation for depth 13, residue 3130. -/
theorem bounds_13_3130 : exactInterval 13 3130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3130 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3130) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3130 : oddCount 3130 13 = 4 ∧ acceleratedOrbit 13 3130 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3130 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3130) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3130.1, data_13_3130.2]

/-- Complete interval computation for depth 13, residue 3131. -/
theorem bounds_13_3131 : exactInterval 13 3131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3131 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3131) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3131 : oddCount 3131 13 = 9 ∧ acceleratedOrbit 13 3131 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3131 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3131) = 3 ^ 9 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3131.1, data_13_3131.2]

/-- Complete interval computation for depth 13, residue 3132. -/
theorem bounds_13_3132 : exactInterval 13 3132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3132 : oddCount 3132 13 = 4 ∧ acceleratedOrbit 13 3132 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3132) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3132.1, data_13_3132.2]

/-- Complete interval computation for depth 13, residue 3133. -/
theorem bounds_13_3133 : exactInterval 13 3133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3133 : oddCount 3133 13 = 4 ∧ acceleratedOrbit 13 3133 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3133) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3133.1, data_13_3133.2]

/-- Complete interval computation for depth 13, residue 3134. -/
theorem bounds_13_3134 : exactInterval 13 3134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3134 : oddCount 3134 13 = 8 ∧ acceleratedOrbit 13 3134 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3134) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3134.1, data_13_3134.2]

/-- Complete interval computation for depth 13, residue 3135. -/
theorem bounds_13_3135 : exactInterval 13 3135 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3135) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3135 : oddCount 3135 13 = 8 ∧ acceleratedOrbit 13 3135 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3135) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3135.1, data_13_3135.2]

/-- Complete interval computation for depth 13, residue 3136. -/
theorem bounds_13_3136 : exactInterval 13 3136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3136 : oddCount 3136 13 = 3 ∧ acceleratedOrbit 13 3136 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3136) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3136.1, data_13_3136.2]

/-- Complete interval computation for depth 13, residue 3137. -/
theorem bounds_13_3137 : exactInterval 13 3137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3137 : oddCount 3137 13 = 6 ∧ acceleratedOrbit 13 3137 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3137) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3137.1, data_13_3137.2]

end Collatz.Research.StoppingAtlas.Batch0671
