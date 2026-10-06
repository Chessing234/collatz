import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0740

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4183. -/
theorem bounds_13_4183 : exactInterval 13 4183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4183 : oddCount 4183 13 = 6 ∧ acceleratedOrbit 13 4183 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4183) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4183.1, data_13_4183.2]

/-- Complete interval computation for depth 13, residue 4184. -/
theorem bounds_13_4184 : exactInterval 13 4184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4184 : oddCount 4184 13 = 5 ∧ acceleratedOrbit 13 4184 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4184) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4184.1, data_13_4184.2]

/-- Complete interval computation for depth 13, residue 4185. -/
theorem bounds_13_4185 : exactInterval 13 4185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4185 : oddCount 4185 13 = 6 ∧ acceleratedOrbit 13 4185 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4185) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4185.1, data_13_4185.2]

/-- Complete interval computation for depth 13, residue 4186. -/
theorem bounds_13_4186 : exactInterval 13 4186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4186 : oddCount 4186 13 = 5 ∧ acceleratedOrbit 13 4186 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4186) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4186.1, data_13_4186.2]

/-- Complete interval computation for depth 13, residue 4187. -/
theorem bounds_13_4187 : exactInterval 13 4187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4187 : oddCount 4187 13 = 9 ∧ acceleratedOrbit 13 4187 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4187) = 3 ^ 9 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4187.1, data_13_4187.2]

/-- Complete interval computation for depth 13, residue 4188. -/
theorem bounds_13_4188 : exactInterval 13 4188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4188 : oddCount 4188 13 = 5 ∧ acceleratedOrbit 13 4188 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4188) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4188.1, data_13_4188.2]

/-- Complete interval computation for depth 13, residue 4189. -/
theorem bounds_13_4189 : exactInterval 13 4189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4189 : oddCount 4189 13 = 5 ∧ acceleratedOrbit 13 4189 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4189) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4189.1, data_13_4189.2]

/-- Complete interval computation for depth 13, residue 4190. -/
theorem bounds_13_4190 : exactInterval 13 4190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4190 : oddCount 4190 13 = 8 ∧ acceleratedOrbit 13 4190 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4190) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4190.1, data_13_4190.2]

/-- Complete interval computation for depth 13, residue 4191. -/
theorem bounds_13_4191 : exactInterval 13 4191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4191 : oddCount 4191 13 = 8 ∧ acceleratedOrbit 13 4191 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4191) = 3 ^ 8 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4191.1, data_13_4191.2]

/-- Complete interval computation for depth 13, residue 4192. -/
theorem bounds_13_4192 : exactInterval 13 4192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4192 : oddCount 4192 13 = 3 ∧ acceleratedOrbit 13 4192 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4192) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4192.1, data_13_4192.2]

/-- Complete interval computation for depth 13, residue 4193. -/
theorem bounds_13_4193 : exactInterval 13 4193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4193 : oddCount 4193 13 = 8 ∧ acceleratedOrbit 13 4193 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4193) = 3 ^ 8 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4193.1, data_13_4193.2]

/-- Complete interval computation for depth 13, residue 4194. -/
theorem bounds_13_4194 : exactInterval 13 4194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4194 : oddCount 4194 13 = 7 ∧ acceleratedOrbit 13 4194 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4194) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4194.1, data_13_4194.2]

/-- Complete interval computation for depth 13, residue 4195. -/
theorem bounds_13_4195 : exactInterval 13 4195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4195 : oddCount 4195 13 = 7 ∧ acceleratedOrbit 13 4195 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4195) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4195.1, data_13_4195.2]

/-- Complete interval computation for depth 13, residue 4196. -/
theorem bounds_13_4196 : exactInterval 13 4196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4196 : oddCount 4196 13 = 7 ∧ acceleratedOrbit 13 4196 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4196) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4196.1, data_13_4196.2]

/-- Complete interval computation for depth 13, residue 4197. -/
theorem bounds_13_4197 : exactInterval 13 4197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4197 : oddCount 4197 13 = 7 ∧ acceleratedOrbit 13 4197 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4197) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4197.1, data_13_4197.2]

end Collatz.Research.StoppingAtlas.Batch0740
