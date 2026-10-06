import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0745

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4259. -/
theorem bounds_13_4259 : exactInterval 13 4259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4259 : oddCount 4259 13 = 6 ∧ acceleratedOrbit 13 4259 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4259) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4259.1, data_13_4259.2]

/-- Complete interval computation for depth 13, residue 4260. -/
theorem bounds_13_4260 : exactInterval 13 4260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4260 : oddCount 4260 13 = 7 ∧ acceleratedOrbit 13 4260 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4260) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4260.1, data_13_4260.2]

/-- Complete interval computation for depth 13, residue 4261. -/
theorem bounds_13_4261 : exactInterval 13 4261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4261 : oddCount 4261 13 = 7 ∧ acceleratedOrbit 13 4261 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4261) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4261.1, data_13_4261.2]

/-- Complete interval computation for depth 13, residue 4262. -/
theorem bounds_13_4262 : exactInterval 13 4262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4262 : oddCount 4262 13 = 7 ∧ acceleratedOrbit 13 4262 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4262) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4262.1, data_13_4262.2]

/-- Complete interval computation for depth 13, residue 4263. -/
theorem bounds_13_4263 : exactInterval 13 4263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4263 : oddCount 4263 13 = 10 ∧ acceleratedOrbit 13 4263 = 30739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4263) = 3 ^ 10 * m + 30739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4263.1, data_13_4263.2]

/-- Complete interval computation for depth 13, residue 4264. -/
theorem bounds_13_4264 : exactInterval 13 4264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4264 : oddCount 4264 13 = 4 ∧ acceleratedOrbit 13 4264 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4264) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4264.1, data_13_4264.2]

/-- Complete interval computation for depth 13, residue 4265. -/
theorem bounds_13_4265 : exactInterval 13 4265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4265 : oddCount 4265 13 = 10 ∧ acceleratedOrbit 13 4265 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4265) = 3 ^ 10 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4265.1, data_13_4265.2]

/-- Complete interval computation for depth 13, residue 4266. -/
theorem bounds_13_4266 : exactInterval 13 4266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4266 : oddCount 4266 13 = 4 ∧ acceleratedOrbit 13 4266 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4266) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4266.1, data_13_4266.2]

/-- Complete interval computation for depth 13, residue 4267. -/
theorem bounds_13_4267 : exactInterval 13 4267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4267 : oddCount 4267 13 = 6 ∧ acceleratedOrbit 13 4267 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4267) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4267.1, data_13_4267.2]

/-- Complete interval computation for depth 13, residue 4268. -/
theorem bounds_13_4268 : exactInterval 13 4268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4268 : oddCount 4268 13 = 5 ∧ acceleratedOrbit 13 4268 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4268) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4268.1, data_13_4268.2]

/-- Complete interval computation for depth 13, residue 4269. -/
theorem bounds_13_4269 : exactInterval 13 4269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4269 : oddCount 4269 13 = 5 ∧ acceleratedOrbit 13 4269 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4269) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4269.1, data_13_4269.2]

/-- Complete interval computation for depth 13, residue 4270. -/
theorem bounds_13_4270 : exactInterval 13 4270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4270 : oddCount 4270 13 = 5 ∧ acceleratedOrbit 13 4270 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4270) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4270.1, data_13_4270.2]

/-- Complete interval computation for depth 13, residue 4271. -/
theorem bounds_13_4271 : exactInterval 13 4271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4271 : oddCount 4271 13 = 8 ∧ acceleratedOrbit 13 4271 = 3422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4271) = 3 ^ 8 * m + 3422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4271.1, data_13_4271.2]

/-- Complete interval computation for depth 13, residue 4272. -/
theorem bounds_13_4272 : exactInterval 13 4272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4272 : oddCount 4272 13 = 5 ∧ acceleratedOrbit 13 4272 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4272) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4272.1, data_13_4272.2]

/-- Complete interval computation for depth 13, residue 4273. -/
theorem bounds_13_4273 : exactInterval 13 4273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4273 : oddCount 4273 13 = 5 ∧ acceleratedOrbit 13 4273 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4273) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4273.1, data_13_4273.2]

/-- Complete interval computation for depth 13, residue 4274. -/
theorem bounds_13_4274 : exactInterval 13 4274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4274 : oddCount 4274 13 = 5 ∧ acceleratedOrbit 13 4274 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4274) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4274.1, data_13_4274.2]

end Collatz.Research.StoppingAtlas.Batch0745
