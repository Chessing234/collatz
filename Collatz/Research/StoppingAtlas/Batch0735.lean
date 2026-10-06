import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0735

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4106. -/
theorem bounds_13_4106 : exactInterval 13 4106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4106 : oddCount 4106 13 = 6 ∧ acceleratedOrbit 13 4106 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4106) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4106.1, data_13_4106.2]

/-- Complete interval computation for depth 13, residue 4107. -/
theorem bounds_13_4107 : exactInterval 13 4107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4107 : oddCount 4107 13 = 5 ∧ acceleratedOrbit 13 4107 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4107) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4107.1, data_13_4107.2]

/-- Complete interval computation for depth 13, residue 4108. -/
theorem bounds_13_4108 : exactInterval 13 4108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4108 : oddCount 4108 13 = 6 ∧ acceleratedOrbit 13 4108 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4108) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4108.1, data_13_4108.2]

/-- Complete interval computation for depth 13, residue 4109. -/
theorem bounds_13_4109 : exactInterval 13 4109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4109 : oddCount 4109 13 = 6 ∧ acceleratedOrbit 13 4109 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4109) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4109.1, data_13_4109.2]

/-- Complete interval computation for depth 13, residue 4110. -/
theorem bounds_13_4110 : exactInterval 13 4110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4110 : oddCount 4110 13 = 5 ∧ acceleratedOrbit 13 4110 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4110) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4110.1, data_13_4110.2]

/-- Complete interval computation for depth 13, residue 4111. -/
theorem bounds_13_4111 : exactInterval 13 4111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4111 : oddCount 4111 13 = 5 ∧ acceleratedOrbit 13 4111 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4111) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4111.1, data_13_4111.2]

/-- Complete interval computation for depth 13, residue 4112. -/
theorem bounds_13_4112 : exactInterval 13 4112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4112 : oddCount 4112 13 = 4 ∧ acceleratedOrbit 13 4112 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4112) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4112.1, data_13_4112.2]

/-- Complete interval computation for depth 13, residue 4113. -/
theorem bounds_13_4113 : exactInterval 13 4113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4113 : oddCount 4113 13 = 6 ∧ acceleratedOrbit 13 4113 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4113) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4113.1, data_13_4113.2]

/-- Complete interval computation for depth 13, residue 4114. -/
theorem bounds_13_4114 : exactInterval 13 4114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4114 : oddCount 4114 13 = 7 ∧ acceleratedOrbit 13 4114 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4114) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4114.1, data_13_4114.2]

/-- Complete interval computation for depth 13, residue 4115. -/
theorem bounds_13_4115 : exactInterval 13 4115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4115 : oddCount 4115 13 = 7 ∧ acceleratedOrbit 13 4115 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4115) = 3 ^ 7 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4115.1, data_13_4115.2]

/-- Complete interval computation for depth 13, residue 4116. -/
theorem bounds_13_4116 : exactInterval 13 4116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4116 : oddCount 4116 13 = 4 ∧ acceleratedOrbit 13 4116 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4116) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4116.1, data_13_4116.2]

/-- Complete interval computation for depth 13, residue 4117. -/
theorem bounds_13_4117 : exactInterval 13 4117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4117 : oddCount 4117 13 = 4 ∧ acceleratedOrbit 13 4117 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4117) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4117.1, data_13_4117.2]

/-- Complete interval computation for depth 13, residue 4118. -/
theorem bounds_13_4118 : exactInterval 13 4118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4118 : oddCount 4118 13 = 6 ∧ acceleratedOrbit 13 4118 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4118) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4118.1, data_13_4118.2]

/-- Complete interval computation for depth 13, residue 4119. -/
theorem bounds_13_4119 : exactInterval 13 4119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4119 : oddCount 4119 13 = 6 ∧ acceleratedOrbit 13 4119 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4119) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4119.1, data_13_4119.2]

/-- Complete interval computation for depth 13, residue 4120. -/
theorem bounds_13_4120 : exactInterval 13 4120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4120 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4120) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4120 : oddCount 4120 13 = 4 ∧ acceleratedOrbit 13 4120 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4120 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4120) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4120.1, data_13_4120.2]

end Collatz.Research.StoppingAtlas.Batch0735
