import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0131

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4259. -/
theorem bounds_15_4259 : exactInterval 15 4259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4259 : oddCount 4259 15 = 6 ∧ acceleratedOrbit 15 4259 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4259) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4259.1, data_15_4259.2]

/-- Complete interval computation for depth 15, residue 4260. -/
theorem bounds_15_4260 : exactInterval 15 4260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4260 : oddCount 4260 15 = 9 ∧ acceleratedOrbit 15 4260 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4260) = 3 ^ 9 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4260.1, data_15_4260.2]

/-- Complete interval computation for depth 15, residue 4261. -/
theorem bounds_15_4261 : exactInterval 15 4261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4261 : oddCount 4261 15 = 9 ∧ acceleratedOrbit 15 4261 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4261) = 3 ^ 9 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4261.1, data_15_4261.2]

/-- Complete interval computation for depth 15, residue 4262. -/
theorem bounds_15_4262 : exactInterval 15 4262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4262 : oddCount 4262 15 = 9 ∧ acceleratedOrbit 15 4262 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4262) = 3 ^ 9 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4262.1, data_15_4262.2]

/-- Complete interval computation for depth 15, residue 4263. -/
theorem bounds_15_4263 : exactInterval 15 4263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4263 : oddCount 4263 15 = 12 ∧ acceleratedOrbit 15 4263 = 69164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4263) = 3 ^ 12 * m + 69164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4263.1, data_15_4263.2]

/-- Complete interval computation for depth 15, residue 4264. -/
theorem bounds_15_4264 : exactInterval 15 4264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4264 : oddCount 4264 15 = 4 ∧ acceleratedOrbit 15 4264 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4264) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4264.1, data_15_4264.2]

/-- Complete interval computation for depth 15, residue 4265. -/
theorem bounds_15_4265 : exactInterval 15 4265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4265 : oddCount 4265 15 = 12 ∧ acceleratedOrbit 15 4265 = 69200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4265) = 3 ^ 12 * m + 69200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4265.1, data_15_4265.2]

/-- Complete interval computation for depth 15, residue 4266. -/
theorem bounds_15_4266 : exactInterval 15 4266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4266 : oddCount 4266 15 = 4 ∧ acceleratedOrbit 15 4266 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4266) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4266.1, data_15_4266.2]

/-- Complete interval computation for depth 15, residue 4267. -/
theorem bounds_15_4267 : exactInterval 15 4267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4267 : oddCount 4267 15 = 6 ∧ acceleratedOrbit 15 4267 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4267) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4267.1, data_15_4267.2]

/-- Complete interval computation for depth 15, residue 4268. -/
theorem bounds_15_4268 : exactInterval 15 4268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4268 : oddCount 4268 15 = 7 ∧ acceleratedOrbit 15 4268 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4268) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4268.1, data_15_4268.2]

/-- Complete interval computation for depth 15, residue 4269. -/
theorem bounds_15_4269 : exactInterval 15 4269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4269 : oddCount 4269 15 = 7 ∧ acceleratedOrbit 15 4269 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4269) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4269.1, data_15_4269.2]

/-- Complete interval computation for depth 15, residue 4270. -/
theorem bounds_15_4270 : exactInterval 15 4270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4270 : oddCount 4270 15 = 7 ∧ acceleratedOrbit 15 4270 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4270) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4270.1, data_15_4270.2]

/-- Complete interval computation for depth 15, residue 4271. -/
theorem bounds_15_4271 : exactInterval 15 4271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4271 : oddCount 4271 15 = 9 ∧ acceleratedOrbit 15 4271 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4271) = 3 ^ 9 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4271.1, data_15_4271.2]

/-- Complete interval computation for depth 15, residue 4272. -/
theorem bounds_15_4272 : exactInterval 15 4272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4272 : oddCount 4272 15 = 5 ∧ acceleratedOrbit 15 4272 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4272) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4272.1, data_15_4272.2]

/-- Complete interval computation for depth 15, residue 4273. -/
theorem bounds_15_4273 : exactInterval 15 4273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4273 : oddCount 4273 15 = 7 ∧ acceleratedOrbit 15 4273 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4273) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4273.1, data_15_4273.2]

/-- Complete interval computation for depth 15, residue 4274. -/
theorem bounds_15_4274 : exactInterval 15 4274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4274 : oddCount 4274 15 = 7 ∧ acceleratedOrbit 15 4274 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4274) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4274.1, data_15_4274.2]

/-- Complete interval computation for depth 15, residue 4275. -/
theorem bounds_15_4275 : exactInterval 15 4275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4275 : oddCount 4275 15 = 7 ∧ acceleratedOrbit 15 4275 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4275) = 3 ^ 7 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4275.1, data_15_4275.2]

/-- Complete interval computation for depth 15, residue 4276. -/
theorem bounds_15_4276 : exactInterval 15 4276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4276 : oddCount 4276 15 = 5 ∧ acceleratedOrbit 15 4276 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4276) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4276.1, data_15_4276.2]

/-- Complete interval computation for depth 15, residue 4277. -/
theorem bounds_15_4277 : exactInterval 15 4277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4277 : oddCount 4277 15 = 5 ∧ acceleratedOrbit 15 4277 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4277) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4277.1, data_15_4277.2]

/-- Complete interval computation for depth 15, residue 4278. -/
theorem bounds_15_4278 : exactInterval 15 4278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4278 : oddCount 4278 15 = 10 ∧ acceleratedOrbit 15 4278 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4278) = 3 ^ 10 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4278.1, data_15_4278.2]

/-- Complete interval computation for depth 15, residue 4279. -/
theorem bounds_15_4279 : exactInterval 15 4279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4279 : oddCount 4279 15 = 10 ∧ acceleratedOrbit 15 4279 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4279) = 3 ^ 10 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4279.1, data_15_4279.2]

/-- Complete interval computation for depth 15, residue 4280. -/
theorem bounds_15_4280 : exactInterval 15 4280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4280 : oddCount 4280 15 = 5 ∧ acceleratedOrbit 15 4280 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4280) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4280.1, data_15_4280.2]

/-- Complete interval computation for depth 15, residue 4281. -/
theorem bounds_15_4281 : exactInterval 15 4281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4281 : oddCount 4281 15 = 7 ∧ acceleratedOrbit 15 4281 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4281) = 3 ^ 7 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4281.1, data_15_4281.2]

/-- Complete interval computation for depth 15, residue 4282. -/
theorem bounds_15_4282 : exactInterval 15 4282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4282 : oddCount 4282 15 = 5 ∧ acceleratedOrbit 15 4282 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4282) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4282.1, data_15_4282.2]

/-- Complete interval computation for depth 15, residue 4283. -/
theorem bounds_15_4283 : exactInterval 15 4283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4283 : oddCount 4283 15 = 7 ∧ acceleratedOrbit 15 4283 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4283) = 3 ^ 7 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4283.1, data_15_4283.2]

/-- Complete interval computation for depth 15, residue 4284. -/
theorem bounds_15_4284 : exactInterval 15 4284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4284 : oddCount 4284 15 = 8 ∧ acceleratedOrbit 15 4284 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4284) = 3 ^ 8 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4284.1, data_15_4284.2]

/-- Complete interval computation for depth 15, residue 4285. -/
theorem bounds_15_4285 : exactInterval 15 4285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4285 : oddCount 4285 15 = 8 ∧ acceleratedOrbit 15 4285 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4285) = 3 ^ 8 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4285.1, data_15_4285.2]

/-- Complete interval computation for depth 15, residue 4286. -/
theorem bounds_15_4286 : exactInterval 15 4286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4286 : oddCount 4286 15 = 8 ∧ acceleratedOrbit 15 4286 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4286) = 3 ^ 8 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4286.1, data_15_4286.2]

/-- Complete interval computation for depth 15, residue 4287. -/
theorem bounds_15_4287 : exactInterval 15 4287 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4287) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4287 : oddCount 4287 15 = 9 ∧ acceleratedOrbit 15 4287 = 2576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4287) = 3 ^ 9 * m + 2576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4287.1, data_15_4287.2]

/-- Complete interval computation for depth 15, residue 4288. -/
theorem bounds_15_4288 : exactInterval 15 4288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4288 : oddCount 4288 15 = 4 ∧ acceleratedOrbit 15 4288 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4288) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4288.1, data_15_4288.2]

/-- Complete interval computation for depth 15, residue 4289. -/
theorem bounds_15_4289 : exactInterval 15 4289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4289 : oddCount 4289 15 = 9 ∧ acceleratedOrbit 15 4289 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4289) = 3 ^ 9 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4289.1, data_15_4289.2]

/-- Complete interval computation for depth 15, residue 4290. -/
theorem bounds_15_4290 : exactInterval 15 4290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4290 : oddCount 4290 15 = 9 ∧ acceleratedOrbit 15 4290 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4290) = 3 ^ 9 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4290.1, data_15_4290.2]

/-- Complete interval computation for depth 15, residue 4291. -/
theorem bounds_15_4291 : exactInterval 15 4291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4291 : oddCount 4291 15 = 9 ∧ acceleratedOrbit 15 4291 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4291) = 3 ^ 9 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4291.1, data_15_4291.2]

end Collatz.Research.PassageAtlas.Batch0131
