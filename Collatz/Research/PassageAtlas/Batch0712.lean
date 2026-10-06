import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0712

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23298. -/
theorem bounds_15_23298 : exactInterval 15 23298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23298 : oddCount 23298 15 = 7 ∧ acceleratedOrbit 15 23298 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23298) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23298.1, data_15_23298.2]

/-- Complete interval computation for depth 15, residue 23299. -/
theorem bounds_15_23299 : exactInterval 15 23299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23299 : oddCount 23299 15 = 7 ∧ acceleratedOrbit 15 23299 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23299) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23299.1, data_15_23299.2]

/-- Complete interval computation for depth 15, residue 23300. -/
theorem bounds_15_23300 : exactInterval 15 23300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23300 : oddCount 23300 15 = 5 ∧ acceleratedOrbit 15 23300 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23300) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23300.1, data_15_23300.2]

/-- Complete interval computation for depth 15, residue 23301. -/
theorem bounds_15_23301 : exactInterval 15 23301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23301 : oddCount 23301 15 = 5 ∧ acceleratedOrbit 15 23301 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23301) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23301.1, data_15_23301.2]

/-- Complete interval computation for depth 15, residue 23302. -/
theorem bounds_15_23302 : exactInterval 15 23302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23302 : oddCount 23302 15 = 5 ∧ acceleratedOrbit 15 23302 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23302) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23302.1, data_15_23302.2]

/-- Complete interval computation for depth 15, residue 23303. -/
theorem bounds_15_23303 : exactInterval 15 23303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23303 : oddCount 23303 15 = 10 ∧ acceleratedOrbit 15 23303 = 41998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23303) = 3 ^ 10 * m + 41998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23303.1, data_15_23303.2]

/-- Complete interval computation for depth 15, residue 23304. -/
theorem bounds_15_23304 : exactInterval 15 23304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23304 : oddCount 23304 15 = 9 ∧ acceleratedOrbit 15 23304 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23304) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23304.1, data_15_23304.2]

/-- Complete interval computation for depth 15, residue 23305. -/
theorem bounds_15_23305 : exactInterval 15 23305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23305 : oddCount 23305 15 = 10 ∧ acceleratedOrbit 15 23305 = 42002 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23305) = 3 ^ 10 * m + 42002 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23305.1, data_15_23305.2]

/-- Complete interval computation for depth 15, residue 23306. -/
theorem bounds_15_23306 : exactInterval 15 23306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23306 : oddCount 23306 15 = 9 ∧ acceleratedOrbit 15 23306 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23306) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23306.1, data_15_23306.2]

/-- Complete interval computation for depth 15, residue 23307. -/
theorem bounds_15_23307 : exactInterval 15 23307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23307 : oddCount 23307 15 = 9 ∧ acceleratedOrbit 15 23307 = 14003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23307) = 3 ^ 9 * m + 14003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23307.1, data_15_23307.2]

/-- Complete interval computation for depth 15, residue 23308. -/
theorem bounds_15_23308 : exactInterval 15 23308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23308 : oddCount 23308 15 = 9 ∧ acceleratedOrbit 15 23308 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23308) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23308.1, data_15_23308.2]

/-- Complete interval computation for depth 15, residue 23309. -/
theorem bounds_15_23309 : exactInterval 15 23309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23309 : oddCount 23309 15 = 9 ∧ acceleratedOrbit 15 23309 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23309) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23309.1, data_15_23309.2]

/-- Complete interval computation for depth 15, residue 23310. -/
theorem bounds_15_23310 : exactInterval 15 23310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23310 : oddCount 23310 15 = 5 ∧ acceleratedOrbit 15 23310 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23310) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23310.1, data_15_23310.2]

/-- Complete interval computation for depth 15, residue 23311. -/
theorem bounds_15_23311 : exactInterval 15 23311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23311 : oddCount 23311 15 = 5 ∧ acceleratedOrbit 15 23311 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23311) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23311.1, data_15_23311.2]

/-- Complete interval computation for depth 15, residue 23312. -/
theorem bounds_15_23312 : exactInterval 15 23312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23312 : oddCount 23312 15 = 4 ∧ acceleratedOrbit 15 23312 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23312) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23312.1, data_15_23312.2]

/-- Complete interval computation for depth 15, residue 23313. -/
theorem bounds_15_23313 : exactInterval 15 23313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23313 : oddCount 23313 15 = 9 ∧ acceleratedOrbit 15 23313 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23313) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23313.1, data_15_23313.2]

/-- Complete interval computation for depth 15, residue 23314. -/
theorem bounds_15_23314 : exactInterval 15 23314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23314 : oddCount 23314 15 = 8 ∧ acceleratedOrbit 15 23314 = 4670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23314) = 3 ^ 8 * m + 4670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23314.1, data_15_23314.2]

/-- Complete interval computation for depth 15, residue 23315. -/
theorem bounds_15_23315 : exactInterval 15 23315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23315 : oddCount 23315 15 = 8 ∧ acceleratedOrbit 15 23315 = 4670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23315) = 3 ^ 8 * m + 4670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23315.1, data_15_23315.2]

/-- Complete interval computation for depth 15, residue 23316. -/
theorem bounds_15_23316 : exactInterval 15 23316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23316 : oddCount 23316 15 = 4 ∧ acceleratedOrbit 15 23316 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23316) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23316.1, data_15_23316.2]

/-- Complete interval computation for depth 15, residue 23317. -/
theorem bounds_15_23317 : exactInterval 15 23317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23317 : oddCount 23317 15 = 4 ∧ acceleratedOrbit 15 23317 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23317) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23317.1, data_15_23317.2]

/-- Complete interval computation for depth 15, residue 23318. -/
theorem bounds_15_23318 : exactInterval 15 23318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23318 : oddCount 23318 15 = 9 ∧ acceleratedOrbit 15 23318 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23318) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23318.1, data_15_23318.2]

/-- Complete interval computation for depth 15, residue 23319. -/
theorem bounds_15_23319 : exactInterval 15 23319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23319 : oddCount 23319 15 = 9 ∧ acceleratedOrbit 15 23319 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23319) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23319.1, data_15_23319.2]

/-- Complete interval computation for depth 15, residue 23320. -/
theorem bounds_15_23320 : exactInterval 15 23320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23320 : oddCount 23320 15 = 4 ∧ acceleratedOrbit 15 23320 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23320) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23320.1, data_15_23320.2]

/-- Complete interval computation for depth 15, residue 23321. -/
theorem bounds_15_23321 : exactInterval 15 23321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23321 : oddCount 23321 15 = 10 ∧ acceleratedOrbit 15 23321 = 42032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23321) = 3 ^ 10 * m + 42032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23321.1, data_15_23321.2]

/-- Complete interval computation for depth 15, residue 23322. -/
theorem bounds_15_23322 : exactInterval 15 23322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23322 : oddCount 23322 15 = 4 ∧ acceleratedOrbit 15 23322 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23322) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23322.1, data_15_23322.2]

/-- Complete interval computation for depth 15, residue 23323. -/
theorem bounds_15_23323 : exactInterval 15 23323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23323 : oddCount 23323 15 = 12 ∧ acceleratedOrbit 15 23323 = 378283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23323) = 3 ^ 12 * m + 378283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23323.1, data_15_23323.2]

/-- Complete interval computation for depth 15, residue 23324. -/
theorem bounds_15_23324 : exactInterval 15 23324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23324 : oddCount 23324 15 = 5 ∧ acceleratedOrbit 15 23324 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23324) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23324.1, data_15_23324.2]

/-- Complete interval computation for depth 15, residue 23325. -/
theorem bounds_15_23325 : exactInterval 15 23325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23325 : oddCount 23325 15 = 5 ∧ acceleratedOrbit 15 23325 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23325) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23325.1, data_15_23325.2]

/-- Complete interval computation for depth 15, residue 23326. -/
theorem bounds_15_23326 : exactInterval 15 23326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23326 : oddCount 23326 15 = 5 ∧ acceleratedOrbit 15 23326 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23326) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23326.1, data_15_23326.2]

/-- Complete interval computation for depth 15, residue 23327. -/
theorem bounds_15_23327 : exactInterval 15 23327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23327 : oddCount 23327 15 = 12 ∧ acceleratedOrbit 15 23327 = 378350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23327) = 3 ^ 12 * m + 378350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23327.1, data_15_23327.2]

/-- Complete interval computation for depth 15, residue 23328. -/
theorem bounds_15_23328 : exactInterval 15 23328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23328 : oddCount 23328 15 = 4 ∧ acceleratedOrbit 15 23328 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23328) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23328.1, data_15_23328.2]

/-- Complete interval computation for depth 15, residue 23329. -/
theorem bounds_15_23329 : exactInterval 15 23329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23329 : oddCount 23329 15 = 8 ∧ acceleratedOrbit 15 23329 = 4673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23329) = 3 ^ 8 * m + 4673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23329.1, data_15_23329.2]

end Collatz.Research.PassageAtlas.Batch0712
