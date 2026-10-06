import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0737

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4136. -/
theorem bounds_13_4136 : exactInterval 13 4136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4136 : oddCount 4136 13 = 5 ∧ acceleratedOrbit 13 4136 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4136) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4136.1, data_13_4136.2]

/-- Complete interval computation for depth 13, residue 4137. -/
theorem bounds_13_4137 : exactInterval 13 4137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4137 : oddCount 4137 13 = 10 ∧ acceleratedOrbit 13 4137 = 29834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4137) = 3 ^ 10 * m + 29834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4137.1, data_13_4137.2]

/-- Complete interval computation for depth 13, residue 4138. -/
theorem bounds_13_4138 : exactInterval 13 4138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4138 : oddCount 4138 13 = 5 ∧ acceleratedOrbit 13 4138 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4138) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4138.1, data_13_4138.2]

/-- Complete interval computation for depth 13, residue 4139. -/
theorem bounds_13_4139 : exactInterval 13 4139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4139 : oddCount 4139 13 = 8 ∧ acceleratedOrbit 13 4139 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4139) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4139.1, data_13_4139.2]

/-- Complete interval computation for depth 13, residue 4140. -/
theorem bounds_13_4140 : exactInterval 13 4140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4140 : oddCount 4140 13 = 4 ∧ acceleratedOrbit 13 4140 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4140) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4140.1, data_13_4140.2]

/-- Complete interval computation for depth 13, residue 4141. -/
theorem bounds_13_4141 : exactInterval 13 4141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4141 : oddCount 4141 13 = 4 ∧ acceleratedOrbit 13 4141 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4141) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4141.1, data_13_4141.2]

/-- Complete interval computation for depth 13, residue 4142. -/
theorem bounds_13_4142 : exactInterval 13 4142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4142 : oddCount 4142 13 = 4 ∧ acceleratedOrbit 13 4142 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4142) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4142.1, data_13_4142.2]

/-- Complete interval computation for depth 13, residue 4143. -/
theorem bounds_13_4143 : exactInterval 13 4143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4143 : oddCount 4143 13 = 9 ∧ acceleratedOrbit 13 4143 = 9958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4143) = 3 ^ 9 * m + 9958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4143.1, data_13_4143.2]

/-- Complete interval computation for depth 13, residue 4144. -/
theorem bounds_13_4144 : exactInterval 13 4144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4144 : oddCount 4144 13 = 5 ∧ acceleratedOrbit 13 4144 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4144) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4144.1, data_13_4144.2]

/-- Complete interval computation for depth 13, residue 4145. -/
theorem bounds_13_4145 : exactInterval 13 4145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4145 : oddCount 4145 13 = 7 ∧ acceleratedOrbit 13 4145 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4145) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4145.1, data_13_4145.2]

/-- Complete interval computation for depth 13, residue 4146. -/
theorem bounds_13_4146 : exactInterval 13 4146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4146 : oddCount 4146 13 = 7 ∧ acceleratedOrbit 13 4146 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4146) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4146.1, data_13_4146.2]

/-- Complete interval computation for depth 13, residue 4147. -/
theorem bounds_13_4147 : exactInterval 13 4147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4147 : oddCount 4147 13 = 7 ∧ acceleratedOrbit 13 4147 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4147) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4147.1, data_13_4147.2]

/-- Complete interval computation for depth 13, residue 4148. -/
theorem bounds_13_4148 : exactInterval 13 4148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4148 : oddCount 4148 13 = 5 ∧ acceleratedOrbit 13 4148 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4148) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4148.1, data_13_4148.2]

/-- Complete interval computation for depth 13, residue 4149. -/
theorem bounds_13_4149 : exactInterval 13 4149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4149 : oddCount 4149 13 = 5 ∧ acceleratedOrbit 13 4149 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4149) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4149.1, data_13_4149.2]

/-- Complete interval computation for depth 13, residue 4150. -/
theorem bounds_13_4150 : exactInterval 13 4150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4150 : oddCount 4150 13 = 8 ∧ acceleratedOrbit 13 4150 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4150) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4150.1, data_13_4150.2]

/-- Complete interval computation for depth 13, residue 4151. -/
theorem bounds_13_4151 : exactInterval 13 4151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4151 : oddCount 4151 13 = 8 ∧ acceleratedOrbit 13 4151 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4151) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4151.1, data_13_4151.2]

end Collatz.Research.StoppingAtlas.Batch0737
