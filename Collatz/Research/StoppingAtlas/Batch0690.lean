import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0690

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3415. -/
theorem bounds_13_3415 : exactInterval 13 3415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3415 : oddCount 3415 13 = 7 ∧ acceleratedOrbit 13 3415 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3415) = 3 ^ 7 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3415.1, data_13_3415.2]

/-- Complete interval computation for depth 13, residue 3416. -/
theorem bounds_13_3416 : exactInterval 13 3416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3416 : oddCount 3416 13 = 7 ∧ acceleratedOrbit 13 3416 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3416) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3416.1, data_13_3416.2]

/-- Complete interval computation for depth 13, residue 3417. -/
theorem bounds_13_3417 : exactInterval 13 3417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3417 : oddCount 3417 13 = 6 ∧ acceleratedOrbit 13 3417 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3417) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3417.1, data_13_3417.2]

/-- Complete interval computation for depth 13, residue 3418. -/
theorem bounds_13_3418 : exactInterval 13 3418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3418 : oddCount 3418 13 = 7 ∧ acceleratedOrbit 13 3418 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3418) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3418.1, data_13_3418.2]

/-- Complete interval computation for depth 13, residue 3419. -/
theorem bounds_13_3419 : exactInterval 13 3419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3419 : oddCount 3419 13 = 8 ∧ acceleratedOrbit 13 3419 = 2740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3419) = 3 ^ 8 * m + 2740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3419.1, data_13_3419.2]

/-- Complete interval computation for depth 13, residue 3420. -/
theorem bounds_13_3420 : exactInterval 13 3420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3420 : oddCount 3420 13 = 7 ∧ acceleratedOrbit 13 3420 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3420) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3420.1, data_13_3420.2]

/-- Complete interval computation for depth 13, residue 3421. -/
theorem bounds_13_3421 : exactInterval 13 3421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3421 : oddCount 3421 13 = 7 ∧ acceleratedOrbit 13 3421 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3421) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3421.1, data_13_3421.2]

/-- Complete interval computation for depth 13, residue 3422. -/
theorem bounds_13_3422 : exactInterval 13 3422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3422 : oddCount 3422 13 = 8 ∧ acceleratedOrbit 13 3422 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3422) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3422.1, data_13_3422.2]

/-- Complete interval computation for depth 13, residue 3423. -/
theorem bounds_13_3423 : exactInterval 13 3423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3423 : oddCount 3423 13 = 8 ∧ acceleratedOrbit 13 3423 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3423) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3423.1, data_13_3423.2]

/-- Complete interval computation for depth 13, residue 3424. -/
theorem bounds_13_3424 : exactInterval 13 3424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3424 : oddCount 3424 13 = 5 ∧ acceleratedOrbit 13 3424 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3424) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3424.1, data_13_3424.2]

/-- Complete interval computation for depth 13, residue 3425. -/
theorem bounds_13_3425 : exactInterval 13 3425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3425 : oddCount 3425 13 = 6 ∧ acceleratedOrbit 13 3425 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3425) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3425.1, data_13_3425.2]

/-- Complete interval computation for depth 13, residue 3426. -/
theorem bounds_13_3426 : exactInterval 13 3426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3426 : oddCount 3426 13 = 4 ∧ acceleratedOrbit 13 3426 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3426) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3426.1, data_13_3426.2]

/-- Complete interval computation for depth 13, residue 3427. -/
theorem bounds_13_3427 : exactInterval 13 3427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3427 : oddCount 3427 13 = 4 ∧ acceleratedOrbit 13 3427 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3427) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3427.1, data_13_3427.2]

/-- Complete interval computation for depth 13, residue 3428. -/
theorem bounds_13_3428 : exactInterval 13 3428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3428 : oddCount 3428 13 = 4 ∧ acceleratedOrbit 13 3428 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3428) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3428.1, data_13_3428.2]

/-- Complete interval computation for depth 13, residue 3429. -/
theorem bounds_13_3429 : exactInterval 13 3429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3429 : oddCount 3429 13 = 4 ∧ acceleratedOrbit 13 3429 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3429) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3429.1, data_13_3429.2]

end Collatz.Research.StoppingAtlas.Batch0690
