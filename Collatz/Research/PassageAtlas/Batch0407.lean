import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0407

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13303. -/
theorem bounds_15_13303 : exactInterval 15 13303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13303 : oddCount 13303 15 = 6 ∧ acceleratedOrbit 15 13303 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13303) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13303.1, data_15_13303.2]

/-- Complete interval computation for depth 15, residue 13304. -/
theorem bounds_15_13304 : exactInterval 15 13304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13304 : oddCount 13304 15 = 10 ∧ acceleratedOrbit 15 13304 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13304) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13304.1, data_15_13304.2]

/-- Complete interval computation for depth 15, residue 13305. -/
theorem bounds_15_13305 : exactInterval 15 13305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13305 : oddCount 13305 15 = 9 ∧ acceleratedOrbit 15 13305 = 7994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13305) = 3 ^ 9 * m + 7994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13305.1, data_15_13305.2]

/-- Complete interval computation for depth 15, residue 13306. -/
theorem bounds_15_13306 : exactInterval 15 13306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13306 : oddCount 13306 15 = 10 ∧ acceleratedOrbit 15 13306 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13306) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13306.1, data_15_13306.2]

/-- Complete interval computation for depth 15, residue 13307. -/
theorem bounds_15_13307 : exactInterval 15 13307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13307 : oddCount 13307 15 = 8 ∧ acceleratedOrbit 15 13307 = 2665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13307) = 3 ^ 8 * m + 2665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13307.1, data_15_13307.2]

/-- Complete interval computation for depth 15, residue 13308. -/
theorem bounds_15_13308 : exactInterval 15 13308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13308 : oddCount 13308 15 = 10 ∧ acceleratedOrbit 15 13308 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13308) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13308.1, data_15_13308.2]

/-- Complete interval computation for depth 15, residue 13309. -/
theorem bounds_15_13309 : exactInterval 15 13309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13309 : oddCount 13309 15 = 10 ∧ acceleratedOrbit 15 13309 = 23989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13309) = 3 ^ 10 * m + 23989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13309.1, data_15_13309.2]

/-- Complete interval computation for depth 15, residue 13310. -/
theorem bounds_15_13310 : exactInterval 15 13310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13310 : oddCount 13310 15 = 11 ∧ acceleratedOrbit 15 13310 = 71966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13310) = 3 ^ 11 * m + 71966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13310.1, data_15_13310.2]

/-- Complete interval computation for depth 15, residue 13311. -/
theorem bounds_15_13311 : exactInterval 15 13311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13311 : oddCount 13311 15 = 11 ∧ acceleratedOrbit 15 13311 = 71966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13311) = 3 ^ 11 * m + 71966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13311.1, data_15_13311.2]

/-- Complete interval computation for depth 15, residue 13312. -/
theorem bounds_15_13312 : exactInterval 15 13312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13312 : oddCount 13312 15 = 2 ∧ acceleratedOrbit 15 13312 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13312) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13312.1, data_15_13312.2]

/-- Complete interval computation for depth 15, residue 13313. -/
theorem bounds_15_13313 : exactInterval 15 13313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13313 : oddCount 13313 15 = 7 ∧ acceleratedOrbit 15 13313 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13313) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13313.1, data_15_13313.2]

/-- Complete interval computation for depth 15, residue 13314. -/
theorem bounds_15_13314 : exactInterval 15 13314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13314 : oddCount 13314 15 = 8 ∧ acceleratedOrbit 15 13314 = 2668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13314) = 3 ^ 8 * m + 2668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13314.1, data_15_13314.2]

/-- Complete interval computation for depth 15, residue 13315. -/
theorem bounds_15_13315 : exactInterval 15 13315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13315 : oddCount 13315 15 = 8 ∧ acceleratedOrbit 15 13315 = 2668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13315) = 3 ^ 8 * m + 2668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13315.1, data_15_13315.2]

/-- Complete interval computation for depth 15, residue 13316. -/
theorem bounds_15_13316 : exactInterval 15 13316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13316 : oddCount 13316 15 = 8 ∧ acceleratedOrbit 15 13316 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13316) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13316.1, data_15_13316.2]

/-- Complete interval computation for depth 15, residue 13317. -/
theorem bounds_15_13317 : exactInterval 15 13317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13317 : oddCount 13317 15 = 8 ∧ acceleratedOrbit 15 13317 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13317) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13317.1, data_15_13317.2]

/-- Complete interval computation for depth 15, residue 13318. -/
theorem bounds_15_13318 : exactInterval 15 13318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13318 : oddCount 13318 15 = 8 ∧ acceleratedOrbit 15 13318 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13318) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13318.1, data_15_13318.2]

/-- Complete interval computation for depth 15, residue 13319. -/
theorem bounds_15_13319 : exactInterval 15 13319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13319 : oddCount 13319 15 = 8 ∧ acceleratedOrbit 15 13319 = 2668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13319) = 3 ^ 8 * m + 2668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13319.1, data_15_13319.2]

/-- Complete interval computation for depth 15, residue 13320. -/
theorem bounds_15_13320 : exactInterval 15 13320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13320 : oddCount 13320 15 = 9 ∧ acceleratedOrbit 15 13320 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13320) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13320.1, data_15_13320.2]

/-- Complete interval computation for depth 15, residue 13321. -/
theorem bounds_15_13321 : exactInterval 15 13321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13321 : oddCount 13321 15 = 8 ∧ acceleratedOrbit 15 13321 = 2668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13321) = 3 ^ 8 * m + 2668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13321.1, data_15_13321.2]

/-- Complete interval computation for depth 15, residue 13322. -/
theorem bounds_15_13322 : exactInterval 15 13322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13322 : oddCount 13322 15 = 9 ∧ acceleratedOrbit 15 13322 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13322) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13322.1, data_15_13322.2]

/-- Complete interval computation for depth 15, residue 13323. -/
theorem bounds_15_13323 : exactInterval 15 13323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13323 : oddCount 13323 15 = 8 ∧ acceleratedOrbit 15 13323 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13323) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13323.1, data_15_13323.2]

/-- Complete interval computation for depth 15, residue 13324. -/
theorem bounds_15_13324 : exactInterval 15 13324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13324 : oddCount 13324 15 = 9 ∧ acceleratedOrbit 15 13324 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13324) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13324.1, data_15_13324.2]

/-- Complete interval computation for depth 15, residue 13325. -/
theorem bounds_15_13325 : exactInterval 15 13325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13325 : oddCount 13325 15 = 9 ∧ acceleratedOrbit 15 13325 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13325) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13325.1, data_15_13325.2]

/-- Complete interval computation for depth 15, residue 13326. -/
theorem bounds_15_13326 : exactInterval 15 13326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13326 : oddCount 13326 15 = 9 ∧ acceleratedOrbit 15 13326 = 8009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13326) = 3 ^ 9 * m + 8009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13326.1, data_15_13326.2]

/-- Complete interval computation for depth 15, residue 13327. -/
theorem bounds_15_13327 : exactInterval 15 13327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13327 : oddCount 13327 15 = 9 ∧ acceleratedOrbit 15 13327 = 8009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13327) = 3 ^ 9 * m + 8009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13327.1, data_15_13327.2]

/-- Complete interval computation for depth 15, residue 13328. -/
theorem bounds_15_13328 : exactInterval 15 13328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13328 : oddCount 13328 15 = 3 ∧ acceleratedOrbit 15 13328 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13328) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13328.1, data_15_13328.2]

/-- Complete interval computation for depth 15, residue 13329. -/
theorem bounds_15_13329 : exactInterval 15 13329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13329 : oddCount 13329 15 = 9 ∧ acceleratedOrbit 15 13329 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13329) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13329.1, data_15_13329.2]

/-- Complete interval computation for depth 15, residue 13330. -/
theorem bounds_15_13330 : exactInterval 15 13330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13330 : oddCount 13330 15 = 8 ∧ acceleratedOrbit 15 13330 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13330) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13330.1, data_15_13330.2]

/-- Complete interval computation for depth 15, residue 13331. -/
theorem bounds_15_13331 : exactInterval 15 13331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13331 : oddCount 13331 15 = 8 ∧ acceleratedOrbit 15 13331 = 2672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13331) = 3 ^ 8 * m + 2672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13331.1, data_15_13331.2]

/-- Complete interval computation for depth 15, residue 13332. -/
theorem bounds_15_13332 : exactInterval 15 13332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13332 : oddCount 13332 15 = 3 ∧ acceleratedOrbit 15 13332 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13332) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13332.1, data_15_13332.2]

/-- Complete interval computation for depth 15, residue 13333. -/
theorem bounds_15_13333 : exactInterval 15 13333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13333 : oddCount 13333 15 = 3 ∧ acceleratedOrbit 15 13333 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13333) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13333.1, data_15_13333.2]

/-- Complete interval computation for depth 15, residue 13334. -/
theorem bounds_15_13334 : exactInterval 15 13334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13334 : oddCount 13334 15 = 9 ∧ acceleratedOrbit 15 13334 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13334) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13334.1, data_15_13334.2]

/-- Complete interval computation for depth 15, residue 13335. -/
theorem bounds_15_13335 : exactInterval 15 13335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13335 : oddCount 13335 15 = 9 ∧ acceleratedOrbit 15 13335 = 8018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13335) = 3 ^ 9 * m + 8018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13335.1, data_15_13335.2]

end Collatz.Research.PassageAtlas.Batch0407
