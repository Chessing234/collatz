import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0132

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4292. -/
theorem bounds_15_4292 : exactInterval 15 4292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4292 : oddCount 4292 15 = 5 ∧ acceleratedOrbit 15 4292 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4292) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4292.1, data_15_4292.2]

/-- Complete interval computation for depth 15, residue 4293. -/
theorem bounds_15_4293 : exactInterval 15 4293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4293 : oddCount 4293 15 = 5 ∧ acceleratedOrbit 15 4293 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4293) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4293.1, data_15_4293.2]

/-- Complete interval computation for depth 15, residue 4294. -/
theorem bounds_15_4294 : exactInterval 15 4294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4294 : oddCount 4294 15 = 5 ∧ acceleratedOrbit 15 4294 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4294) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4294.1, data_15_4294.2]

/-- Complete interval computation for depth 15, residue 4295. -/
theorem bounds_15_4295 : exactInterval 15 4295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4295 : oddCount 4295 15 = 9 ∧ acceleratedOrbit 15 4295 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4295) = 3 ^ 9 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4295.1, data_15_4295.2]

/-- Complete interval computation for depth 15, residue 4296. -/
theorem bounds_15_4296 : exactInterval 15 4296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4296 : oddCount 4296 15 = 5 ∧ acceleratedOrbit 15 4296 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4296) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4296.1, data_15_4296.2]

/-- Complete interval computation for depth 15, residue 4297. -/
theorem bounds_15_4297 : exactInterval 15 4297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4297 : oddCount 4297 15 = 5 ∧ acceleratedOrbit 15 4297 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4297) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4297.1, data_15_4297.2]

/-- Complete interval computation for depth 15, residue 4298. -/
theorem bounds_15_4298 : exactInterval 15 4298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4298 : oddCount 4298 15 = 5 ∧ acceleratedOrbit 15 4298 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4298) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4298.1, data_15_4298.2]

/-- Complete interval computation for depth 15, residue 4299. -/
theorem bounds_15_4299 : exactInterval 15 4299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4299 : oddCount 4299 15 = 8 ∧ acceleratedOrbit 15 4299 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4299) = 3 ^ 8 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4299.1, data_15_4299.2]

/-- Complete interval computation for depth 15, residue 4300. -/
theorem bounds_15_4300 : exactInterval 15 4300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4300 : oddCount 4300 15 = 5 ∧ acceleratedOrbit 15 4300 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4300) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4300.1, data_15_4300.2]

/-- Complete interval computation for depth 15, residue 4301. -/
theorem bounds_15_4301 : exactInterval 15 4301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4301 : oddCount 4301 15 = 5 ∧ acceleratedOrbit 15 4301 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4301) = 3 ^ 5 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4301.1, data_15_4301.2]

/-- Complete interval computation for depth 15, residue 4302. -/
theorem bounds_15_4302 : exactInterval 15 4302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4302 : oddCount 4302 15 = 11 ∧ acceleratedOrbit 15 4302 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4302) = 3 ^ 11 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4302.1, data_15_4302.2]

/-- Complete interval computation for depth 15, residue 4303. -/
theorem bounds_15_4303 : exactInterval 15 4303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4303 : oddCount 4303 15 = 11 ∧ acceleratedOrbit 15 4303 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4303) = 3 ^ 11 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4303.1, data_15_4303.2]

/-- Complete interval computation for depth 15, residue 4304. -/
theorem bounds_15_4304 : exactInterval 15 4304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4304 : oddCount 4304 15 = 4 ∧ acceleratedOrbit 15 4304 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4304) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4304.1, data_15_4304.2]

/-- Complete interval computation for depth 15, residue 4305. -/
theorem bounds_15_4305 : exactInterval 15 4305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4305 : oddCount 4305 15 = 9 ∧ acceleratedOrbit 15 4305 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4305) = 3 ^ 9 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4305.1, data_15_4305.2]

/-- Complete interval computation for depth 15, residue 4306. -/
theorem bounds_15_4306 : exactInterval 15 4306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4306 : oddCount 4306 15 = 9 ∧ acceleratedOrbit 15 4306 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4306) = 3 ^ 9 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4306.1, data_15_4306.2]

/-- Complete interval computation for depth 15, residue 4307. -/
theorem bounds_15_4307 : exactInterval 15 4307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4307 : oddCount 4307 15 = 9 ∧ acceleratedOrbit 15 4307 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4307) = 3 ^ 9 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4307.1, data_15_4307.2]

/-- Complete interval computation for depth 15, residue 4308. -/
theorem bounds_15_4308 : exactInterval 15 4308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4308 : oddCount 4308 15 = 4 ∧ acceleratedOrbit 15 4308 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4308) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4308.1, data_15_4308.2]

/-- Complete interval computation for depth 15, residue 4309. -/
theorem bounds_15_4309 : exactInterval 15 4309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4309 : oddCount 4309 15 = 4 ∧ acceleratedOrbit 15 4309 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4309) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4309.1, data_15_4309.2]

/-- Complete interval computation for depth 15, residue 4310. -/
theorem bounds_15_4310 : exactInterval 15 4310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4310 : oddCount 4310 15 = 11 ∧ acceleratedOrbit 15 4310 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4310) = 3 ^ 11 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4310.1, data_15_4310.2]

/-- Complete interval computation for depth 15, residue 4311. -/
theorem bounds_15_4311 : exactInterval 15 4311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4311 : oddCount 4311 15 = 11 ∧ acceleratedOrbit 15 4311 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4311) = 3 ^ 11 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4311.1, data_15_4311.2]

/-- Complete interval computation for depth 15, residue 4312. -/
theorem bounds_15_4312 : exactInterval 15 4312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4312 : oddCount 4312 15 = 8 ∧ acceleratedOrbit 15 4312 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4312) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4312.1, data_15_4312.2]

/-- Complete interval computation for depth 15, residue 4313. -/
theorem bounds_15_4313 : exactInterval 15 4313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4313 : oddCount 4313 15 = 8 ∧ acceleratedOrbit 15 4313 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4313) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4313.1, data_15_4313.2]

/-- Complete interval computation for depth 15, residue 4314. -/
theorem bounds_15_4314 : exactInterval 15 4314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4314 : oddCount 4314 15 = 8 ∧ acceleratedOrbit 15 4314 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4314) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4314.1, data_15_4314.2]

/-- Complete interval computation for depth 15, residue 4315. -/
theorem bounds_15_4315 : exactInterval 15 4315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4315 : oddCount 4315 15 = 9 ∧ acceleratedOrbit 15 4315 = 2594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4315) = 3 ^ 9 * m + 2594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4315.1, data_15_4315.2]

/-- Complete interval computation for depth 15, residue 4316. -/
theorem bounds_15_4316 : exactInterval 15 4316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4316 : oddCount 4316 15 = 8 ∧ acceleratedOrbit 15 4316 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4316) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4316.1, data_15_4316.2]

/-- Complete interval computation for depth 15, residue 4317. -/
theorem bounds_15_4317 : exactInterval 15 4317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4317 : oddCount 4317 15 = 8 ∧ acceleratedOrbit 15 4317 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4317) = 3 ^ 8 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4317.1, data_15_4317.2]

/-- Complete interval computation for depth 15, residue 4318. -/
theorem bounds_15_4318 : exactInterval 15 4318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4318 : oddCount 4318 15 = 10 ∧ acceleratedOrbit 15 4318 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4318) = 3 ^ 10 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4318.1, data_15_4318.2]

/-- Complete interval computation for depth 15, residue 4319. -/
theorem bounds_15_4319 : exactInterval 15 4319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4319 : oddCount 4319 15 = 10 ∧ acceleratedOrbit 15 4319 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4319) = 3 ^ 10 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4319.1, data_15_4319.2]

/-- Complete interval computation for depth 15, residue 4320. -/
theorem bounds_15_4320 : exactInterval 15 4320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4320 : oddCount 4320 15 = 6 ∧ acceleratedOrbit 15 4320 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4320) = 3 ^ 6 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4320.1, data_15_4320.2]

/-- Complete interval computation for depth 15, residue 4321. -/
theorem bounds_15_4321 : exactInterval 15 4321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4321 : oddCount 4321 15 = 9 ∧ acceleratedOrbit 15 4321 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4321) = 3 ^ 9 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4321.1, data_15_4321.2]

/-- Complete interval computation for depth 15, residue 4322. -/
theorem bounds_15_4322 : exactInterval 15 4322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4322 : oddCount 4322 15 = 4 ∧ acceleratedOrbit 15 4322 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4322) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4322.1, data_15_4322.2]

/-- Complete interval computation for depth 15, residue 4323. -/
theorem bounds_15_4323 : exactInterval 15 4323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4323 : oddCount 4323 15 = 4 ∧ acceleratedOrbit 15 4323 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4323) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4323.1, data_15_4323.2]

/-- Complete interval computation for depth 15, residue 4324. -/
theorem bounds_15_4324 : exactInterval 15 4324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4324 : oddCount 4324 15 = 7 ∧ acceleratedOrbit 15 4324 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4324) = 3 ^ 7 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4324.1, data_15_4324.2]

end Collatz.Research.PassageAtlas.Batch0132
