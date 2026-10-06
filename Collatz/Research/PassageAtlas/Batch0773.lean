import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0773

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25296. -/
theorem bounds_15_25296 : exactInterval 15 25296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25296 : oddCount 25296 15 = 6 ∧ acceleratedOrbit 15 25296 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25296) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25296.1, data_15_25296.2]

/-- Complete interval computation for depth 15, residue 25297. -/
theorem bounds_15_25297 : exactInterval 15 25297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25297 : oddCount 25297 15 = 6 ∧ acceleratedOrbit 15 25297 = 563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25297) = 3 ^ 6 * m + 563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25297.1, data_15_25297.2]

/-- Complete interval computation for depth 15, residue 25298. -/
theorem bounds_15_25298 : exactInterval 15 25298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25298 : oddCount 25298 15 = 6 ∧ acceleratedOrbit 15 25298 = 563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25298) = 3 ^ 6 * m + 563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25298.1, data_15_25298.2]

/-- Complete interval computation for depth 15, residue 25299. -/
theorem bounds_15_25299 : exactInterval 15 25299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25299 : oddCount 25299 15 = 6 ∧ acceleratedOrbit 15 25299 = 563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25299) = 3 ^ 6 * m + 563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25299.1, data_15_25299.2]

/-- Complete interval computation for depth 15, residue 25300. -/
theorem bounds_15_25300 : exactInterval 15 25300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25300 : oddCount 25300 15 = 6 ∧ acceleratedOrbit 15 25300 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25300) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25300.1, data_15_25300.2]

/-- Complete interval computation for depth 15, residue 25301. -/
theorem bounds_15_25301 : exactInterval 15 25301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25301 : oddCount 25301 15 = 6 ∧ acceleratedOrbit 15 25301 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25301) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25301.1, data_15_25301.2]

/-- Complete interval computation for depth 15, residue 25302. -/
theorem bounds_15_25302 : exactInterval 15 25302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25302 : oddCount 25302 15 = 6 ∧ acceleratedOrbit 15 25302 = 563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25302) = 3 ^ 6 * m + 563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25302.1, data_15_25302.2]

/-- Complete interval computation for depth 15, residue 25303. -/
theorem bounds_15_25303 : exactInterval 15 25303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25303 : oddCount 25303 15 = 6 ∧ acceleratedOrbit 15 25303 = 563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25303) = 3 ^ 6 * m + 563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25303.1, data_15_25303.2]

/-- Complete interval computation for depth 15, residue 25304. -/
theorem bounds_15_25304 : exactInterval 15 25304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25304 : oddCount 25304 15 = 8 ∧ acceleratedOrbit 15 25304 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25304) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25304.1, data_15_25304.2]

/-- Complete interval computation for depth 15, residue 25305. -/
theorem bounds_15_25305 : exactInterval 15 25305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25305 : oddCount 25305 15 = 7 ∧ acceleratedOrbit 15 25305 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25305) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25305.1, data_15_25305.2]

/-- Complete interval computation for depth 15, residue 25306. -/
theorem bounds_15_25306 : exactInterval 15 25306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25306 : oddCount 25306 15 = 8 ∧ acceleratedOrbit 15 25306 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25306) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25306.1, data_15_25306.2]

/-- Complete interval computation for depth 15, residue 25307. -/
theorem bounds_15_25307 : exactInterval 15 25307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25307 : oddCount 25307 15 = 9 ∧ acceleratedOrbit 15 25307 = 15203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25307) = 3 ^ 9 * m + 15203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25307.1, data_15_25307.2]

/-- Complete interval computation for depth 15, residue 25308. -/
theorem bounds_15_25308 : exactInterval 15 25308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25308 : oddCount 25308 15 = 8 ∧ acceleratedOrbit 15 25308 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25308) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25308.1, data_15_25308.2]

/-- Complete interval computation for depth 15, residue 25309. -/
theorem bounds_15_25309 : exactInterval 15 25309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25309 : oddCount 25309 15 = 8 ∧ acceleratedOrbit 15 25309 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25309) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25309.1, data_15_25309.2]

/-- Complete interval computation for depth 15, residue 25310. -/
theorem bounds_15_25310 : exactInterval 15 25310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25310 : oddCount 25310 15 = 8 ∧ acceleratedOrbit 15 25310 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25310) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25310.1, data_15_25310.2]

/-- Complete interval computation for depth 15, residue 25311. -/
theorem bounds_15_25311 : exactInterval 15 25311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25311 : oddCount 25311 15 = 8 ∧ acceleratedOrbit 15 25311 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25311) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25311.1, data_15_25311.2]

/-- Complete interval computation for depth 15, residue 25312. -/
theorem bounds_15_25312 : exactInterval 15 25312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25312 : oddCount 25312 15 = 6 ∧ acceleratedOrbit 15 25312 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25312) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25312.1, data_15_25312.2]

/-- Complete interval computation for depth 15, residue 25313. -/
theorem bounds_15_25313 : exactInterval 15 25313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25313 : oddCount 25313 15 = 10 ∧ acceleratedOrbit 15 25313 = 45620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25313) = 3 ^ 10 * m + 45620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25313.1, data_15_25313.2]

/-- Complete interval computation for depth 15, residue 25314. -/
theorem bounds_15_25314 : exactInterval 15 25314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25314 : oddCount 25314 15 = 6 ∧ acceleratedOrbit 15 25314 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25314) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25314.1, data_15_25314.2]

/-- Complete interval computation for depth 15, residue 25315. -/
theorem bounds_15_25315 : exactInterval 15 25315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25315 : oddCount 25315 15 = 6 ∧ acceleratedOrbit 15 25315 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25315) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25315.1, data_15_25315.2]

/-- Complete interval computation for depth 15, residue 25316. -/
theorem bounds_15_25316 : exactInterval 15 25316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25316 : oddCount 25316 15 = 7 ∧ acceleratedOrbit 15 25316 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25316) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25316.1, data_15_25316.2]

/-- Complete interval computation for depth 15, residue 25317. -/
theorem bounds_15_25317 : exactInterval 15 25317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25317 : oddCount 25317 15 = 7 ∧ acceleratedOrbit 15 25317 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25317) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25317.1, data_15_25317.2]

/-- Complete interval computation for depth 15, residue 25318. -/
theorem bounds_15_25318 : exactInterval 15 25318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25318 : oddCount 25318 15 = 7 ∧ acceleratedOrbit 15 25318 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25318) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25318.1, data_15_25318.2]

/-- Complete interval computation for depth 15, residue 25319. -/
theorem bounds_15_25319 : exactInterval 15 25319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25319 : oddCount 25319 15 = 11 ∧ acceleratedOrbit 15 25319 = 136885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25319) = 3 ^ 11 * m + 136885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25319.1, data_15_25319.2]

/-- Complete interval computation for depth 15, residue 25320. -/
theorem bounds_15_25320 : exactInterval 15 25320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25320 : oddCount 25320 15 = 6 ∧ acceleratedOrbit 15 25320 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25320) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25320.1, data_15_25320.2]

/-- Complete interval computation for depth 15, residue 25321. -/
theorem bounds_15_25321 : exactInterval 15 25321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25321 : oddCount 25321 15 = 9 ∧ acceleratedOrbit 15 25321 = 15211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25321) = 3 ^ 9 * m + 15211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25321.1, data_15_25321.2]

/-- Complete interval computation for depth 15, residue 25322. -/
theorem bounds_15_25322 : exactInterval 15 25322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25322 : oddCount 25322 15 = 6 ∧ acceleratedOrbit 15 25322 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25322) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25322.1, data_15_25322.2]

/-- Complete interval computation for depth 15, residue 25323. -/
theorem bounds_15_25323 : exactInterval 15 25323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25323 : oddCount 25323 15 = 8 ∧ acceleratedOrbit 15 25323 = 5071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25323) = 3 ^ 8 * m + 5071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25323.1, data_15_25323.2]

/-- Complete interval computation for depth 15, residue 25324. -/
theorem bounds_15_25324 : exactInterval 15 25324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25324 : oddCount 25324 15 = 9 ∧ acceleratedOrbit 15 25324 = 15218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25324) = 3 ^ 9 * m + 15218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25324.1, data_15_25324.2]

/-- Complete interval computation for depth 15, residue 25325. -/
theorem bounds_15_25325 : exactInterval 15 25325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25325 : oddCount 25325 15 = 9 ∧ acceleratedOrbit 15 25325 = 15218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25325) = 3 ^ 9 * m + 15218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25325.1, data_15_25325.2]

/-- Complete interval computation for depth 15, residue 25326. -/
theorem bounds_15_25326 : exactInterval 15 25326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25326 : oddCount 25326 15 = 9 ∧ acceleratedOrbit 15 25326 = 15218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25326) = 3 ^ 9 * m + 15218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25326.1, data_15_25326.2]

/-- Complete interval computation for depth 15, residue 25327. -/
theorem bounds_15_25327 : exactInterval 15 25327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25327 : oddCount 25327 15 = 11 ∧ acceleratedOrbit 15 25327 = 136927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25327) = 3 ^ 11 * m + 136927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25327.1, data_15_25327.2]

/-- Complete interval computation for depth 15, residue 25328. -/
theorem bounds_15_25328 : exactInterval 15 25328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25328 : oddCount 25328 15 = 9 ∧ acceleratedOrbit 15 25328 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25328) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25328.1, data_15_25328.2]

end Collatz.Research.PassageAtlas.Batch0773
