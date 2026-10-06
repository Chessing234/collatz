import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0686

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3353. -/
theorem bounds_13_3353 : exactInterval 13 3353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3353 : oddCount 3353 13 = 7 ∧ acceleratedOrbit 13 3353 = 896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3353) = 3 ^ 7 * m + 896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3353.1, data_13_3353.2]

/-- Complete interval computation for depth 13, residue 3354. -/
theorem bounds_13_3354 : exactInterval 13 3354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3354 : oddCount 3354 13 = 5 ∧ acceleratedOrbit 13 3354 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3354) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3354.1, data_13_3354.2]

/-- Complete interval computation for depth 13, residue 3355. -/
theorem bounds_13_3355 : exactInterval 13 3355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3355 : oddCount 3355 13 = 10 ∧ acceleratedOrbit 13 3355 = 24194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3355) = 3 ^ 10 * m + 24194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3355.1, data_13_3355.2]

/-- Complete interval computation for depth 13, residue 3356. -/
theorem bounds_13_3356 : exactInterval 13 3356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3356 : oddCount 3356 13 = 8 ∧ acceleratedOrbit 13 3356 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3356) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3356.1, data_13_3356.2]

/-- Complete interval computation for depth 13, residue 3357. -/
theorem bounds_13_3357 : exactInterval 13 3357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3357 : oddCount 3357 13 = 8 ∧ acceleratedOrbit 13 3357 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3357) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3357.1, data_13_3357.2]

/-- Complete interval computation for depth 13, residue 3358. -/
theorem bounds_13_3358 : exactInterval 13 3358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3358 : oddCount 3358 13 = 8 ∧ acceleratedOrbit 13 3358 = 2693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3358) = 3 ^ 8 * m + 2693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3358.1, data_13_3358.2]

/-- Complete interval computation for depth 13, residue 3359. -/
theorem bounds_13_3359 : exactInterval 13 3359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3359 : oddCount 3359 13 = 6 ∧ acceleratedOrbit 13 3359 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3359) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3359.1, data_13_3359.2]

/-- Complete interval computation for depth 13, residue 3360. -/
theorem bounds_13_3360 : exactInterval 13 3360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3360 : oddCount 3360 13 = 5 ∧ acceleratedOrbit 13 3360 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3360) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3360.1, data_13_3360.2]

/-- Complete interval computation for depth 13, residue 3361. -/
theorem bounds_13_3361 : exactInterval 13 3361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3361 : oddCount 3361 13 = 5 ∧ acceleratedOrbit 13 3361 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3361) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3361.1, data_13_3361.2]

/-- Complete interval computation for depth 13, residue 3362. -/
theorem bounds_13_3362 : exactInterval 13 3362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3362 : oddCount 3362 13 = 5 ∧ acceleratedOrbit 13 3362 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3362) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3362.1, data_13_3362.2]

/-- Complete interval computation for depth 13, residue 3363. -/
theorem bounds_13_3363 : exactInterval 13 3363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3363 : oddCount 3363 13 = 5 ∧ acceleratedOrbit 13 3363 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3363) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3363.1, data_13_3363.2]

/-- Complete interval computation for depth 13, residue 3364. -/
theorem bounds_13_3364 : exactInterval 13 3364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3364 : oddCount 3364 13 = 5 ∧ acceleratedOrbit 13 3364 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3364) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3364.1, data_13_3364.2]

/-- Complete interval computation for depth 13, residue 3365. -/
theorem bounds_13_3365 : exactInterval 13 3365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3365 : oddCount 3365 13 = 5 ∧ acceleratedOrbit 13 3365 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3365) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3365.1, data_13_3365.2]

/-- Complete interval computation for depth 13, residue 3366. -/
theorem bounds_13_3366 : exactInterval 13 3366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3366 : oddCount 3366 13 = 5 ∧ acceleratedOrbit 13 3366 = 100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3366) = 3 ^ 5 * m + 100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3366.1, data_13_3366.2]

/-- Complete interval computation for depth 13, residue 3367. -/
theorem bounds_13_3367 : exactInterval 13 3367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3367 : oddCount 3367 13 = 8 ∧ acceleratedOrbit 13 3367 = 2699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3367) = 3 ^ 8 * m + 2699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3367.1, data_13_3367.2]

end Collatz.Research.StoppingAtlas.Batch0686
