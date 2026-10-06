import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0669

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3092. -/
theorem bounds_13_3092 : exactInterval 13 3092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3092 : oddCount 3092 13 = 4 ∧ acceleratedOrbit 13 3092 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3092) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3092.1, data_13_3092.2]

/-- Complete interval computation for depth 13, residue 3093. -/
theorem bounds_13_3093 : exactInterval 13 3093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3093 : oddCount 3093 13 = 4 ∧ acceleratedOrbit 13 3093 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3093) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3093.1, data_13_3093.2]

/-- Complete interval computation for depth 13, residue 3094. -/
theorem bounds_13_3094 : exactInterval 13 3094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3094 : oddCount 3094 13 = 5 ∧ acceleratedOrbit 13 3094 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3094) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3094.1, data_13_3094.2]

/-- Complete interval computation for depth 13, residue 3095. -/
theorem bounds_13_3095 : exactInterval 13 3095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3095 : oddCount 3095 13 = 5 ∧ acceleratedOrbit 13 3095 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3095) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3095.1, data_13_3095.2]

/-- Complete interval computation for depth 13, residue 3096. -/
theorem bounds_13_3096 : exactInterval 13 3096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3096 : oddCount 3096 13 = 4 ∧ acceleratedOrbit 13 3096 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3096) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3096.1, data_13_3096.2]

/-- Complete interval computation for depth 13, residue 3097. -/
theorem bounds_13_3097 : exactInterval 13 3097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3097 : oddCount 3097 13 = 9 ∧ acceleratedOrbit 13 3097 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3097) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3097.1, data_13_3097.2]

/-- Complete interval computation for depth 13, residue 3098. -/
theorem bounds_13_3098 : exactInterval 13 3098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3098 : oddCount 3098 13 = 4 ∧ acceleratedOrbit 13 3098 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3098) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3098.1, data_13_3098.2]

/-- Complete interval computation for depth 13, residue 3099. -/
theorem bounds_13_3099 : exactInterval 13 3099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3099 : oddCount 3099 13 = 10 ∧ acceleratedOrbit 13 3099 = 22349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3099) = 3 ^ 10 * m + 22349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3099.1, data_13_3099.2]

/-- Complete interval computation for depth 13, residue 3100. -/
theorem bounds_13_3100 : exactInterval 13 3100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3100 : oddCount 3100 13 = 7 ∧ acceleratedOrbit 13 3100 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3100) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3100.1, data_13_3100.2]

/-- Complete interval computation for depth 13, residue 3101. -/
theorem bounds_13_3101 : exactInterval 13 3101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3101 : oddCount 3101 13 = 7 ∧ acceleratedOrbit 13 3101 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3101) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3101.1, data_13_3101.2]

/-- Complete interval computation for depth 13, residue 3102. -/
theorem bounds_13_3102 : exactInterval 13 3102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3102 : oddCount 3102 13 = 7 ∧ acceleratedOrbit 13 3102 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3102) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3102.1, data_13_3102.2]

/-- Complete interval computation for depth 13, residue 3103. -/
theorem bounds_13_3103 : exactInterval 13 3103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3103 : oddCount 3103 13 = 10 ∧ acceleratedOrbit 13 3103 = 22376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3103) = 3 ^ 10 * m + 22376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3103.1, data_13_3103.2]

/-- Complete interval computation for depth 13, residue 3104. -/
theorem bounds_13_3104 : exactInterval 13 3104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3104 : oddCount 3104 13 = 5 ∧ acceleratedOrbit 13 3104 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3104) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3104.1, data_13_3104.2]

/-- Complete interval computation for depth 13, residue 3105. -/
theorem bounds_13_3105 : exactInterval 13 3105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3105 : oddCount 3105 13 = 7 ∧ acceleratedOrbit 13 3105 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3105) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3105.1, data_13_3105.2]

/-- Complete interval computation for depth 13, residue 3106. -/
theorem bounds_13_3106 : exactInterval 13 3106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3106 : oddCount 3106 13 = 4 ∧ acceleratedOrbit 13 3106 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3106) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3106.1, data_13_3106.2]

end Collatz.Research.StoppingAtlas.Batch0669
