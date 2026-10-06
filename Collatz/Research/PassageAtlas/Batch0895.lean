import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0895

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29294. -/
theorem bounds_15_29294 : exactInterval 15 29294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29294 : oddCount 29294 15 = 9 ∧ acceleratedOrbit 15 29294 = 17599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29294) = 3 ^ 9 * m + 17599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29294.1, data_15_29294.2]

/-- Complete interval computation for depth 15, residue 29295. -/
theorem bounds_15_29295 : exactInterval 15 29295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29295 : oddCount 29295 15 = 11 ∧ acceleratedOrbit 15 29295 = 158381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29295) = 3 ^ 11 * m + 158381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29295.1, data_15_29295.2]

/-- Complete interval computation for depth 15, residue 29296. -/
theorem bounds_15_29296 : exactInterval 15 29296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29296 : oddCount 29296 15 = 7 ∧ acceleratedOrbit 15 29296 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29296) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29296.1, data_15_29296.2]

/-- Complete interval computation for depth 15, residue 29297. -/
theorem bounds_15_29297 : exactInterval 15 29297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29297 : oddCount 29297 15 = 5 ∧ acceleratedOrbit 15 29297 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29297) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29297.1, data_15_29297.2]

/-- Complete interval computation for depth 15, residue 29298. -/
theorem bounds_15_29298 : exactInterval 15 29298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29298 : oddCount 29298 15 = 9 ∧ acceleratedOrbit 15 29298 = 17603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29298) = 3 ^ 9 * m + 17603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29298.1, data_15_29298.2]

/-- Complete interval computation for depth 15, residue 29299. -/
theorem bounds_15_29299 : exactInterval 15 29299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29299 : oddCount 29299 15 = 9 ∧ acceleratedOrbit 15 29299 = 17603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29299) = 3 ^ 9 * m + 17603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29299.1, data_15_29299.2]

/-- Complete interval computation for depth 15, residue 29300. -/
theorem bounds_15_29300 : exactInterval 15 29300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29300 : oddCount 29300 15 = 7 ∧ acceleratedOrbit 15 29300 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29300) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29300.1, data_15_29300.2]

/-- Complete interval computation for depth 15, residue 29301. -/
theorem bounds_15_29301 : exactInterval 15 29301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29301 : oddCount 29301 15 = 7 ∧ acceleratedOrbit 15 29301 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29301) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29301.1, data_15_29301.2]

/-- Complete interval computation for depth 15, residue 29302. -/
theorem bounds_15_29302 : exactInterval 15 29302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29302 : oddCount 29302 15 = 7 ∧ acceleratedOrbit 15 29302 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29302) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29302.1, data_15_29302.2]

/-- Complete interval computation for depth 15, residue 29303. -/
theorem bounds_15_29303 : exactInterval 15 29303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29303 : oddCount 29303 15 = 7 ∧ acceleratedOrbit 15 29303 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29303) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29303.1, data_15_29303.2]

/-- Complete interval computation for depth 15, residue 29304. -/
theorem bounds_15_29304 : exactInterval 15 29304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29304 : oddCount 29304 15 = 7 ∧ acceleratedOrbit 15 29304 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29304) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29304.1, data_15_29304.2]

/-- Complete interval computation for depth 15, residue 29305. -/
theorem bounds_15_29305 : exactInterval 15 29305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29305 : oddCount 29305 15 = 6 ∧ acceleratedOrbit 15 29305 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29305) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29305.1, data_15_29305.2]

/-- Complete interval computation for depth 15, residue 29306. -/
theorem bounds_15_29306 : exactInterval 15 29306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29306 : oddCount 29306 15 = 7 ∧ acceleratedOrbit 15 29306 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29306) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29306.1, data_15_29306.2]

/-- Complete interval computation for depth 15, residue 29307. -/
theorem bounds_15_29307 : exactInterval 15 29307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29307 : oddCount 29307 15 = 8 ∧ acceleratedOrbit 15 29307 = 5869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29307) = 3 ^ 8 * m + 5869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29307.1, data_15_29307.2]

/-- Complete interval computation for depth 15, residue 29308. -/
theorem bounds_15_29308 : exactInterval 15 29308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29308 : oddCount 29308 15 = 10 ∧ acceleratedOrbit 15 29308 = 52822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29308) = 3 ^ 10 * m + 52822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29308.1, data_15_29308.2]

/-- Complete interval computation for depth 15, residue 29309. -/
theorem bounds_15_29309 : exactInterval 15 29309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29309 : oddCount 29309 15 = 10 ∧ acceleratedOrbit 15 29309 = 52822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29309) = 3 ^ 10 * m + 52822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29309.1, data_15_29309.2]

/-- Complete interval computation for depth 15, residue 29310. -/
theorem bounds_15_29310 : exactInterval 15 29310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29310 : oddCount 29310 15 = 10 ∧ acceleratedOrbit 15 29310 = 52822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29310) = 3 ^ 10 * m + 52822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29310.1, data_15_29310.2]

/-- Complete interval computation for depth 15, residue 29311. -/
theorem bounds_15_29311 : exactInterval 15 29311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29311 : oddCount 29311 15 = 11 ∧ acceleratedOrbit 15 29311 = 158464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29311) = 3 ^ 11 * m + 158464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29311.1, data_15_29311.2]

/-- Complete interval computation for depth 15, residue 29312. -/
theorem bounds_15_29312 : exactInterval 15 29312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29312 : oddCount 29312 15 = 4 ∧ acceleratedOrbit 15 29312 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29312) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29312.1, data_15_29312.2]

/-- Complete interval computation for depth 15, residue 29313. -/
theorem bounds_15_29313 : exactInterval 15 29313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29313 : oddCount 29313 15 = 8 ∧ acceleratedOrbit 15 29313 = 5870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29313) = 3 ^ 8 * m + 5870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29313.1, data_15_29313.2]

/-- Complete interval computation for depth 15, residue 29314. -/
theorem bounds_15_29314 : exactInterval 15 29314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29314 : oddCount 29314 15 = 5 ∧ acceleratedOrbit 15 29314 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29314) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29314.1, data_15_29314.2]

/-- Complete interval computation for depth 15, residue 29315. -/
theorem bounds_15_29315 : exactInterval 15 29315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29315 : oddCount 29315 15 = 5 ∧ acceleratedOrbit 15 29315 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29315) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29315.1, data_15_29315.2]

/-- Complete interval computation for depth 15, residue 29316. -/
theorem bounds_15_29316 : exactInterval 15 29316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29316 : oddCount 29316 15 = 9 ∧ acceleratedOrbit 15 29316 = 17617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29316) = 3 ^ 9 * m + 17617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29316.1, data_15_29316.2]

/-- Complete interval computation for depth 15, residue 29317. -/
theorem bounds_15_29317 : exactInterval 15 29317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29317 : oddCount 29317 15 = 9 ∧ acceleratedOrbit 15 29317 = 17617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29317) = 3 ^ 9 * m + 17617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29317.1, data_15_29317.2]

/-- Complete interval computation for depth 15, residue 29318. -/
theorem bounds_15_29318 : exactInterval 15 29318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29318 : oddCount 29318 15 = 9 ∧ acceleratedOrbit 15 29318 = 17617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29318) = 3 ^ 9 * m + 17617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29318.1, data_15_29318.2]

/-- Complete interval computation for depth 15, residue 29319. -/
theorem bounds_15_29319 : exactInterval 15 29319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29319 : oddCount 29319 15 = 8 ∧ acceleratedOrbit 15 29319 = 5872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29319) = 3 ^ 8 * m + 5872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29319.1, data_15_29319.2]

/-- Complete interval computation for depth 15, residue 29320. -/
theorem bounds_15_29320 : exactInterval 15 29320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29320 : oddCount 29320 15 = 6 ∧ acceleratedOrbit 15 29320 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29320) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29320.1, data_15_29320.2]

/-- Complete interval computation for depth 15, residue 29321. -/
theorem bounds_15_29321 : exactInterval 15 29321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29321 : oddCount 29321 15 = 9 ∧ acceleratedOrbit 15 29321 = 17614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29321) = 3 ^ 9 * m + 17614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29321.1, data_15_29321.2]

/-- Complete interval computation for depth 15, residue 29322. -/
theorem bounds_15_29322 : exactInterval 15 29322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29322 : oddCount 29322 15 = 6 ∧ acceleratedOrbit 15 29322 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29322) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29322.1, data_15_29322.2]

/-- Complete interval computation for depth 15, residue 29323. -/
theorem bounds_15_29323 : exactInterval 15 29323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29323 : oddCount 29323 15 = 9 ∧ acceleratedOrbit 15 29323 = 17617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29323) = 3 ^ 9 * m + 17617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29323.1, data_15_29323.2]

/-- Complete interval computation for depth 15, residue 29324. -/
theorem bounds_15_29324 : exactInterval 15 29324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29324 : oddCount 29324 15 = 6 ∧ acceleratedOrbit 15 29324 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29324) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29324.1, data_15_29324.2]

/-- Complete interval computation for depth 15, residue 29325. -/
theorem bounds_15_29325 : exactInterval 15 29325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29325 : oddCount 29325 15 = 6 ∧ acceleratedOrbit 15 29325 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29325) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29325.1, data_15_29325.2]

/-- Complete interval computation for depth 15, residue 29326. -/
theorem bounds_15_29326 : exactInterval 15 29326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29326 : oddCount 29326 15 = 11 ∧ acceleratedOrbit 15 29326 = 158557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29326) = 3 ^ 11 * m + 158557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29326.1, data_15_29326.2]

end Collatz.Research.PassageAtlas.Batch0895
