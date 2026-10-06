import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0127

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4128. -/
theorem bounds_15_4128 : exactInterval 15 4128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4128 : oddCount 4128 15 = 6 ∧ acceleratedOrbit 15 4128 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4128) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4128.1, data_15_4128.2]

/-- Complete interval computation for depth 15, residue 4129. -/
theorem bounds_15_4129 : exactInterval 15 4129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4129 : oddCount 4129 15 = 10 ∧ acceleratedOrbit 15 4129 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4129) = 3 ^ 10 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4129.1, data_15_4129.2]

/-- Complete interval computation for depth 15, residue 4130. -/
theorem bounds_15_4130 : exactInterval 15 4130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4130 : oddCount 4130 15 = 5 ∧ acceleratedOrbit 15 4130 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4130) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4130.1, data_15_4130.2]

/-- Complete interval computation for depth 15, residue 4131. -/
theorem bounds_15_4131 : exactInterval 15 4131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4131 : oddCount 4131 15 = 5 ∧ acceleratedOrbit 15 4131 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4131) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4131.1, data_15_4131.2]

/-- Complete interval computation for depth 15, residue 4132. -/
theorem bounds_15_4132 : exactInterval 15 4132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4132 : oddCount 4132 15 = 8 ∧ acceleratedOrbit 15 4132 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4132) = 3 ^ 8 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4132.1, data_15_4132.2]

/-- Complete interval computation for depth 15, residue 4133. -/
theorem bounds_15_4133 : exactInterval 15 4133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4133 : oddCount 4133 15 = 8 ∧ acceleratedOrbit 15 4133 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4133) = 3 ^ 8 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4133.1, data_15_4133.2]

/-- Complete interval computation for depth 15, residue 4134. -/
theorem bounds_15_4134 : exactInterval 15 4134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4134 : oddCount 4134 15 = 8 ∧ acceleratedOrbit 15 4134 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4134) = 3 ^ 8 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4134.1, data_15_4134.2]

/-- Complete interval computation for depth 15, residue 4135. -/
theorem bounds_15_4135 : exactInterval 15 4135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4135 : oddCount 4135 15 = 9 ∧ acceleratedOrbit 15 4135 = 2486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4135) = 3 ^ 9 * m + 2486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4135.1, data_15_4135.2]

/-- Complete interval computation for depth 15, residue 4136. -/
theorem bounds_15_4136 : exactInterval 15 4136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4136 : oddCount 4136 15 = 6 ∧ acceleratedOrbit 15 4136 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4136) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4136.1, data_15_4136.2]

/-- Complete interval computation for depth 15, residue 4137. -/
theorem bounds_15_4137 : exactInterval 15 4137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4137 : oddCount 4137 15 = 11 ∧ acceleratedOrbit 15 4137 = 22376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4137) = 3 ^ 11 * m + 22376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4137.1, data_15_4137.2]

/-- Complete interval computation for depth 15, residue 4138. -/
theorem bounds_15_4138 : exactInterval 15 4138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4138 : oddCount 4138 15 = 6 ∧ acceleratedOrbit 15 4138 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4138) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4138.1, data_15_4138.2]

/-- Complete interval computation for depth 15, residue 4139. -/
theorem bounds_15_4139 : exactInterval 15 4139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4139 : oddCount 4139 15 = 8 ∧ acceleratedOrbit 15 4139 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4139) = 3 ^ 8 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4139.1, data_15_4139.2]

/-- Complete interval computation for depth 15, residue 4140. -/
theorem bounds_15_4140 : exactInterval 15 4140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4140 : oddCount 4140 15 = 5 ∧ acceleratedOrbit 15 4140 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4140) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4140.1, data_15_4140.2]

/-- Complete interval computation for depth 15, residue 4141. -/
theorem bounds_15_4141 : exactInterval 15 4141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4141 : oddCount 4141 15 = 5 ∧ acceleratedOrbit 15 4141 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4141) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4141.1, data_15_4141.2]

/-- Complete interval computation for depth 15, residue 4142. -/
theorem bounds_15_4142 : exactInterval 15 4142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4142 : oddCount 4142 15 = 5 ∧ acceleratedOrbit 15 4142 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4142) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4142.1, data_15_4142.2]

/-- Complete interval computation for depth 15, residue 4143. -/
theorem bounds_15_4143 : exactInterval 15 4143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4143 : oddCount 4143 15 = 10 ∧ acceleratedOrbit 15 4143 = 7469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4143) = 3 ^ 10 * m + 7469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4143.1, data_15_4143.2]

/-- Complete interval computation for depth 15, residue 4144. -/
theorem bounds_15_4144 : exactInterval 15 4144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4144 : oddCount 4144 15 = 6 ∧ acceleratedOrbit 15 4144 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4144) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4144.1, data_15_4144.2]

/-- Complete interval computation for depth 15, residue 4145. -/
theorem bounds_15_4145 : exactInterval 15 4145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4145 : oddCount 4145 15 = 8 ∧ acceleratedOrbit 15 4145 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4145) = 3 ^ 8 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4145.1, data_15_4145.2]

/-- Complete interval computation for depth 15, residue 4146. -/
theorem bounds_15_4146 : exactInterval 15 4146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4146 : oddCount 4146 15 = 8 ∧ acceleratedOrbit 15 4146 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4146) = 3 ^ 8 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4146.1, data_15_4146.2]

/-- Complete interval computation for depth 15, residue 4147. -/
theorem bounds_15_4147 : exactInterval 15 4147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4147 : oddCount 4147 15 = 8 ∧ acceleratedOrbit 15 4147 = 832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4147) = 3 ^ 8 * m + 832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4147.1, data_15_4147.2]

/-- Complete interval computation for depth 15, residue 4148. -/
theorem bounds_15_4148 : exactInterval 15 4148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4148 : oddCount 4148 15 = 6 ∧ acceleratedOrbit 15 4148 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4148) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4148.1, data_15_4148.2]

/-- Complete interval computation for depth 15, residue 4149. -/
theorem bounds_15_4149 : exactInterval 15 4149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4149 : oddCount 4149 15 = 6 ∧ acceleratedOrbit 15 4149 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4149) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4149.1, data_15_4149.2]

/-- Complete interval computation for depth 15, residue 4150. -/
theorem bounds_15_4150 : exactInterval 15 4150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4150 : oddCount 4150 15 = 9 ∧ acceleratedOrbit 15 4150 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4150) = 3 ^ 9 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4150.1, data_15_4150.2]

/-- Complete interval computation for depth 15, residue 4151. -/
theorem bounds_15_4151 : exactInterval 15 4151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4151 : oddCount 4151 15 = 9 ∧ acceleratedOrbit 15 4151 = 2495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4151) = 3 ^ 9 * m + 2495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4151.1, data_15_4151.2]

/-- Complete interval computation for depth 15, residue 4152. -/
theorem bounds_15_4152 : exactInterval 15 4152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4152 : oddCount 4152 15 = 8 ∧ acceleratedOrbit 15 4152 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4152) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4152.1, data_15_4152.2]

/-- Complete interval computation for depth 15, residue 4153. -/
theorem bounds_15_4153 : exactInterval 15 4153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4153 : oddCount 4153 15 = 7 ∧ acceleratedOrbit 15 4153 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4153) = 3 ^ 7 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4153.1, data_15_4153.2]

/-- Complete interval computation for depth 15, residue 4154. -/
theorem bounds_15_4154 : exactInterval 15 4154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4154 : oddCount 4154 15 = 8 ∧ acceleratedOrbit 15 4154 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4154) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4154.1, data_15_4154.2]

/-- Complete interval computation for depth 15, residue 4155. -/
theorem bounds_15_4155 : exactInterval 15 4155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4155 : oddCount 4155 15 = 7 ∧ acceleratedOrbit 15 4155 = 278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4155) = 3 ^ 7 * m + 278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4155.1, data_15_4155.2]

/-- Complete interval computation for depth 15, residue 4156. -/
theorem bounds_15_4156 : exactInterval 15 4156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4156 : oddCount 4156 15 = 8 ∧ acceleratedOrbit 15 4156 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4156) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4156.1, data_15_4156.2]

/-- Complete interval computation for depth 15, residue 4157. -/
theorem bounds_15_4157 : exactInterval 15 4157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4157 : oddCount 4157 15 = 8 ∧ acceleratedOrbit 15 4157 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4157) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4157.1, data_15_4157.2]

/-- Complete interval computation for depth 15, residue 4158. -/
theorem bounds_15_4158 : exactInterval 15 4158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4158 : oddCount 4158 15 = 8 ∧ acceleratedOrbit 15 4158 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4158) = 3 ^ 8 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4158.1, data_15_4158.2]

/-- Complete interval computation for depth 15, residue 4159. -/
theorem bounds_15_4159 : exactInterval 15 4159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4159 : oddCount 4159 15 = 8 ∧ acceleratedOrbit 15 4159 = 833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4159) = 3 ^ 8 * m + 833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4159.1, data_15_4159.2]

/-- Complete interval computation for depth 15, residue 4160. -/
theorem bounds_15_4160 : exactInterval 15 4160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4160 : oddCount 4160 15 = 4 ∧ acceleratedOrbit 15 4160 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4160) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4160.1, data_15_4160.2]

end Collatz.Research.PassageAtlas.Batch0127
