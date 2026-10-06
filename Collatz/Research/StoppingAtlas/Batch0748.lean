import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0748

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4305. -/
theorem bounds_13_4305 : exactInterval 13 4305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4305 : oddCount 4305 13 = 7 ∧ acceleratedOrbit 13 4305 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4305) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4305.1, data_13_4305.2]

/-- Complete interval computation for depth 13, residue 4306. -/
theorem bounds_13_4306 : exactInterval 13 4306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4306 : oddCount 4306 13 = 7 ∧ acceleratedOrbit 13 4306 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4306) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4306.1, data_13_4306.2]

/-- Complete interval computation for depth 13, residue 4307. -/
theorem bounds_13_4307 : exactInterval 13 4307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4307 : oddCount 4307 13 = 7 ∧ acceleratedOrbit 13 4307 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4307) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4307.1, data_13_4307.2]

/-- Complete interval computation for depth 13, residue 4308. -/
theorem bounds_13_4308 : exactInterval 13 4308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4308 : oddCount 4308 13 = 4 ∧ acceleratedOrbit 13 4308 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4308) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4308.1, data_13_4308.2]

/-- Complete interval computation for depth 13, residue 4309. -/
theorem bounds_13_4309 : exactInterval 13 4309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4309 : oddCount 4309 13 = 4 ∧ acceleratedOrbit 13 4309 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4309) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4309.1, data_13_4309.2]

/-- Complete interval computation for depth 13, residue 4310. -/
theorem bounds_13_4310 : exactInterval 13 4310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4310 : oddCount 4310 13 = 9 ∧ acceleratedOrbit 13 4310 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4310) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4310.1, data_13_4310.2]

/-- Complete interval computation for depth 13, residue 4311. -/
theorem bounds_13_4311 : exactInterval 13 4311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4311 : oddCount 4311 13 = 9 ∧ acceleratedOrbit 13 4311 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4311) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4311.1, data_13_4311.2]

/-- Complete interval computation for depth 13, residue 4312. -/
theorem bounds_13_4312 : exactInterval 13 4312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4312 : oddCount 4312 13 = 7 ∧ acceleratedOrbit 13 4312 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4312) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4312.1, data_13_4312.2]

/-- Complete interval computation for depth 13, residue 4313. -/
theorem bounds_13_4313 : exactInterval 13 4313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4313 : oddCount 4313 13 = 7 ∧ acceleratedOrbit 13 4313 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4313) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4313.1, data_13_4313.2]

/-- Complete interval computation for depth 13, residue 4314. -/
theorem bounds_13_4314 : exactInterval 13 4314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4314 : oddCount 4314 13 = 7 ∧ acceleratedOrbit 13 4314 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4314) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4314.1, data_13_4314.2]

/-- Complete interval computation for depth 13, residue 4315. -/
theorem bounds_13_4315 : exactInterval 13 4315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4315 : oddCount 4315 13 = 8 ∧ acceleratedOrbit 13 4315 = 3458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4315) = 3 ^ 8 * m + 3458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4315.1, data_13_4315.2]

/-- Complete interval computation for depth 13, residue 4316. -/
theorem bounds_13_4316 : exactInterval 13 4316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4316 : oddCount 4316 13 = 7 ∧ acceleratedOrbit 13 4316 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4316) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4316.1, data_13_4316.2]

/-- Complete interval computation for depth 13, residue 4317. -/
theorem bounds_13_4317 : exactInterval 13 4317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4317 : oddCount 4317 13 = 7 ∧ acceleratedOrbit 13 4317 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4317) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4317.1, data_13_4317.2]

/-- Complete interval computation for depth 13, residue 4318. -/
theorem bounds_13_4318 : exactInterval 13 4318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4318 : oddCount 4318 13 = 9 ∧ acceleratedOrbit 13 4318 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4318) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4318.1, data_13_4318.2]

/-- Complete interval computation for depth 13, residue 4319. -/
theorem bounds_13_4319 : exactInterval 13 4319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4319 : oddCount 4319 13 = 9 ∧ acceleratedOrbit 13 4319 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4319) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4319.1, data_13_4319.2]

/-- Complete interval computation for depth 13, residue 4320. -/
theorem bounds_13_4320 : exactInterval 13 4320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4320 : oddCount 4320 13 = 4 ∧ acceleratedOrbit 13 4320 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4320) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4320.1, data_13_4320.2]

end Collatz.Research.StoppingAtlas.Batch0748
