import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0813

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5304. -/
theorem bounds_13_5304 : exactInterval 13 5304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5304 : oddCount 5304 13 = 4 ∧ acceleratedOrbit 13 5304 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5304) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5304.1, data_13_5304.2]

/-- Complete interval computation for depth 13, residue 5305. -/
theorem bounds_13_5305 : exactInterval 13 5305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5305 : oddCount 5305 13 = 8 ∧ acceleratedOrbit 13 5305 = 4252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5305) = 3 ^ 8 * m + 4252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5305.1, data_13_5305.2]

/-- Complete interval computation for depth 13, residue 5306. -/
theorem bounds_13_5306 : exactInterval 13 5306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5306 : oddCount 5306 13 = 4 ∧ acceleratedOrbit 13 5306 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5306) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5306.1, data_13_5306.2]

/-- Complete interval computation for depth 13, residue 5307. -/
theorem bounds_13_5307 : exactInterval 13 5307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5307 : oddCount 5307 13 = 9 ∧ acceleratedOrbit 13 5307 = 12757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5307) = 3 ^ 9 * m + 12757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5307.1, data_13_5307.2]

/-- Complete interval computation for depth 13, residue 5308. -/
theorem bounds_13_5308 : exactInterval 13 5308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5308 : oddCount 5308 13 = 8 ∧ acceleratedOrbit 13 5308 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5308) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5308.1, data_13_5308.2]

/-- Complete interval computation for depth 13, residue 5309. -/
theorem bounds_13_5309 : exactInterval 13 5309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5309 : oddCount 5309 13 = 8 ∧ acceleratedOrbit 13 5309 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5309) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5309.1, data_13_5309.2]

/-- Complete interval computation for depth 13, residue 5310. -/
theorem bounds_13_5310 : exactInterval 13 5310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5310 : oddCount 5310 13 = 8 ∧ acceleratedOrbit 13 5310 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5310) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5310.1, data_13_5310.2]

/-- Complete interval computation for depth 13, residue 5311. -/
theorem bounds_13_5311 : exactInterval 13 5311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5311 : oddCount 5311 13 = 9 ∧ acceleratedOrbit 13 5311 = 12764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5311) = 3 ^ 9 * m + 12764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5311.1, data_13_5311.2]

/-- Complete interval computation for depth 13, residue 5312. -/
theorem bounds_13_5312 : exactInterval 13 5312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5312 : oddCount 5312 13 = 5 ∧ acceleratedOrbit 13 5312 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5312) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5312.1, data_13_5312.2]

/-- Complete interval computation for depth 13, residue 5313. -/
theorem bounds_13_5313 : exactInterval 13 5313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5313 : oddCount 5313 13 = 7 ∧ acceleratedOrbit 13 5313 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5313) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5313.1, data_13_5313.2]

/-- Complete interval computation for depth 13, residue 5314. -/
theorem bounds_13_5314 : exactInterval 13 5314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5314 : oddCount 5314 13 = 7 ∧ acceleratedOrbit 13 5314 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5314) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5314.1, data_13_5314.2]

/-- Complete interval computation for depth 13, residue 5315. -/
theorem bounds_13_5315 : exactInterval 13 5315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5315 : oddCount 5315 13 = 7 ∧ acceleratedOrbit 13 5315 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5315) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5315.1, data_13_5315.2]

/-- Complete interval computation for depth 13, residue 5316. -/
theorem bounds_13_5316 : exactInterval 13 5316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5316 : oddCount 5316 13 = 6 ∧ acceleratedOrbit 13 5316 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5316) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5316.1, data_13_5316.2]

/-- Complete interval computation for depth 13, residue 5317. -/
theorem bounds_13_5317 : exactInterval 13 5317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5317 : oddCount 5317 13 = 6 ∧ acceleratedOrbit 13 5317 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5317) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5317.1, data_13_5317.2]

/-- Complete interval computation for depth 13, residue 5318. -/
theorem bounds_13_5318 : exactInterval 13 5318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5318 : oddCount 5318 13 = 6 ∧ acceleratedOrbit 13 5318 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5318) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5318.1, data_13_5318.2]

end Collatz.Research.StoppingAtlas.Batch0813
