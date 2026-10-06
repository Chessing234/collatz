import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0227

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7405. -/
theorem bounds_15_7405 : exactInterval 15 7405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7405 : oddCount 7405 15 = 5 ∧ acceleratedOrbit 15 7405 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7405) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7405.1, data_15_7405.2]

/-- Complete interval computation for depth 15, residue 7406. -/
theorem bounds_15_7406 : exactInterval 15 7406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7406 : oddCount 7406 15 = 5 ∧ acceleratedOrbit 15 7406 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7406) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7406.1, data_15_7406.2]

/-- Complete interval computation for depth 15, residue 7407. -/
theorem bounds_15_7407 : exactInterval 15 7407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7407 : oddCount 7407 15 = 12 ∧ acceleratedOrbit 15 7407 = 120149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7407) = 3 ^ 12 * m + 120149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7407.1, data_15_7407.2]

/-- Complete interval computation for depth 15, residue 7408. -/
theorem bounds_15_7408 : exactInterval 15 7408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7408 : oddCount 7408 15 = 7 ∧ acceleratedOrbit 15 7408 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7408) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7408.1, data_15_7408.2]

/-- Complete interval computation for depth 15, residue 7409. -/
theorem bounds_15_7409 : exactInterval 15 7409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7409 : oddCount 7409 15 = 7 ∧ acceleratedOrbit 15 7409 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7409) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7409.1, data_15_7409.2]

/-- Complete interval computation for depth 15, residue 7410. -/
theorem bounds_15_7410 : exactInterval 15 7410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7410 : oddCount 7410 15 = 10 ∧ acceleratedOrbit 15 7410 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7410) = 3 ^ 10 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7410.1, data_15_7410.2]

/-- Complete interval computation for depth 15, residue 7411. -/
theorem bounds_15_7411 : exactInterval 15 7411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7411 : oddCount 7411 15 = 10 ∧ acceleratedOrbit 15 7411 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7411) = 3 ^ 10 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7411.1, data_15_7411.2]

/-- Complete interval computation for depth 15, residue 7412. -/
theorem bounds_15_7412 : exactInterval 15 7412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7412 : oddCount 7412 15 = 7 ∧ acceleratedOrbit 15 7412 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7412) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7412.1, data_15_7412.2]

/-- Complete interval computation for depth 15, residue 7413. -/
theorem bounds_15_7413 : exactInterval 15 7413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7413 : oddCount 7413 15 = 7 ∧ acceleratedOrbit 15 7413 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7413) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7413.1, data_15_7413.2]

/-- Complete interval computation for depth 15, residue 7414. -/
theorem bounds_15_7414 : exactInterval 15 7414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7414 : oddCount 7414 15 = 5 ∧ acceleratedOrbit 15 7414 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7414) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7414.1, data_15_7414.2]

/-- Complete interval computation for depth 15, residue 7415. -/
theorem bounds_15_7415 : exactInterval 15 7415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7415 : oddCount 7415 15 = 5 ∧ acceleratedOrbit 15 7415 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7415) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7415.1, data_15_7415.2]

/-- Complete interval computation for depth 15, residue 7416. -/
theorem bounds_15_7416 : exactInterval 15 7416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7416 : oddCount 7416 15 = 8 ∧ acceleratedOrbit 15 7416 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7416) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7416.1, data_15_7416.2]

/-- Complete interval computation for depth 15, residue 7417. -/
theorem bounds_15_7417 : exactInterval 15 7417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7417 : oddCount 7417 15 = 8 ∧ acceleratedOrbit 15 7417 = 1486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7417) = 3 ^ 8 * m + 1486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7417.1, data_15_7417.2]

/-- Complete interval computation for depth 15, residue 7418. -/
theorem bounds_15_7418 : exactInterval 15 7418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7418 : oddCount 7418 15 = 8 ∧ acceleratedOrbit 15 7418 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7418) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7418.1, data_15_7418.2]

/-- Complete interval computation for depth 15, residue 7419. -/
theorem bounds_15_7419 : exactInterval 15 7419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7419 : oddCount 7419 15 = 10 ∧ acceleratedOrbit 15 7419 = 13373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7419) = 3 ^ 10 * m + 13373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7419.1, data_15_7419.2]

/-- Complete interval computation for depth 15, residue 7420. -/
theorem bounds_15_7420 : exactInterval 15 7420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7420 : oddCount 7420 15 = 8 ∧ acceleratedOrbit 15 7420 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7420) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7420.1, data_15_7420.2]

/-- Complete interval computation for depth 15, residue 7421. -/
theorem bounds_15_7421 : exactInterval 15 7421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7421 : oddCount 7421 15 = 8 ∧ acceleratedOrbit 15 7421 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7421) = 3 ^ 8 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7421.1, data_15_7421.2]

/-- Complete interval computation for depth 15, residue 7422. -/
theorem bounds_15_7422 : exactInterval 15 7422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7422 : oddCount 7422 15 = 12 ∧ acceleratedOrbit 15 7422 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7422) = 3 ^ 12 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7422.1, data_15_7422.2]

/-- Complete interval computation for depth 15, residue 7423. -/
theorem bounds_15_7423 : exactInterval 15 7423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7423 : oddCount 7423 15 = 12 ∧ acceleratedOrbit 15 7423 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7423) = 3 ^ 12 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7423.1, data_15_7423.2]

/-- Complete interval computation for depth 15, residue 7424. -/
theorem bounds_15_7424 : exactInterval 15 7424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7424 : oddCount 7424 15 = 4 ∧ acceleratedOrbit 15 7424 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7424) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7424.1, data_15_7424.2]

/-- Complete interval computation for depth 15, residue 7425. -/
theorem bounds_15_7425 : exactInterval 15 7425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7425 : oddCount 7425 15 = 7 ∧ acceleratedOrbit 15 7425 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7425) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7425.1, data_15_7425.2]

/-- Complete interval computation for depth 15, residue 7426. -/
theorem bounds_15_7426 : exactInterval 15 7426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7426 : oddCount 7426 15 = 9 ∧ acceleratedOrbit 15 7426 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7426) = 3 ^ 9 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7426.1, data_15_7426.2]

/-- Complete interval computation for depth 15, residue 7427. -/
theorem bounds_15_7427 : exactInterval 15 7427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7427 : oddCount 7427 15 = 9 ∧ acceleratedOrbit 15 7427 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7427) = 3 ^ 9 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7427.1, data_15_7427.2]

/-- Complete interval computation for depth 15, residue 7428. -/
theorem bounds_15_7428 : exactInterval 15 7428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7428 : oddCount 7428 15 = 5 ∧ acceleratedOrbit 15 7428 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7428) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7428.1, data_15_7428.2]

/-- Complete interval computation for depth 15, residue 7429. -/
theorem bounds_15_7429 : exactInterval 15 7429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7429 : oddCount 7429 15 = 5 ∧ acceleratedOrbit 15 7429 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7429) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7429.1, data_15_7429.2]

/-- Complete interval computation for depth 15, residue 7430. -/
theorem bounds_15_7430 : exactInterval 15 7430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7430 : oddCount 7430 15 = 5 ∧ acceleratedOrbit 15 7430 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7430) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7430.1, data_15_7430.2]

/-- Complete interval computation for depth 15, residue 7431. -/
theorem bounds_15_7431 : exactInterval 15 7431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7431 : oddCount 7431 15 = 9 ∧ acceleratedOrbit 15 7431 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7431) = 3 ^ 9 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7431.1, data_15_7431.2]

/-- Complete interval computation for depth 15, residue 7432. -/
theorem bounds_15_7432 : exactInterval 15 7432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7432 : oddCount 7432 15 = 6 ∧ acceleratedOrbit 15 7432 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7432) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7432.1, data_15_7432.2]

/-- Complete interval computation for depth 15, residue 7433. -/
theorem bounds_15_7433 : exactInterval 15 7433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7433 : oddCount 7433 15 = 8 ∧ acceleratedOrbit 15 7433 = 1489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7433) = 3 ^ 8 * m + 1489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7433.1, data_15_7433.2]

/-- Complete interval computation for depth 15, residue 7434. -/
theorem bounds_15_7434 : exactInterval 15 7434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7434 : oddCount 7434 15 = 6 ∧ acceleratedOrbit 15 7434 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7434) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7434.1, data_15_7434.2]

/-- Complete interval computation for depth 15, residue 7435. -/
theorem bounds_15_7435 : exactInterval 15 7435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7435 : oddCount 7435 15 = 7 ∧ acceleratedOrbit 15 7435 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7435) = 3 ^ 7 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7435.1, data_15_7435.2]

/-- Complete interval computation for depth 15, residue 7436. -/
theorem bounds_15_7436 : exactInterval 15 7436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7436 : oddCount 7436 15 = 6 ∧ acceleratedOrbit 15 7436 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7436) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7436.1, data_15_7436.2]

/-- Complete interval computation for depth 15, residue 7437. -/
theorem bounds_15_7437 : exactInterval 15 7437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7437 : oddCount 7437 15 = 6 ∧ acceleratedOrbit 15 7437 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7437) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7437.1, data_15_7437.2]

end Collatz.Research.PassageAtlas.Batch0227
