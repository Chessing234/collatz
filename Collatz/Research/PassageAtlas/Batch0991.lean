import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0991

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32440. -/
theorem bounds_15_32440 : exactInterval 15 32440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32440 : oddCount 32440 15 = 8 ∧ acceleratedOrbit 15 32440 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32440) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32440.1, data_15_32440.2]

/-- Complete interval computation for depth 15, residue 32441. -/
theorem bounds_15_32441 : exactInterval 15 32441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32441 : oddCount 32441 15 = 8 ∧ acceleratedOrbit 15 32441 = 6497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32441) = 3 ^ 8 * m + 6497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32441.1, data_15_32441.2]

/-- Complete interval computation for depth 15, residue 32442. -/
theorem bounds_15_32442 : exactInterval 15 32442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32442 : oddCount 32442 15 = 8 ∧ acceleratedOrbit 15 32442 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32442) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32442.1, data_15_32442.2]

/-- Complete interval computation for depth 15, residue 32443. -/
theorem bounds_15_32443 : exactInterval 15 32443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32443 : oddCount 32443 15 = 8 ∧ acceleratedOrbit 15 32443 = 6497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32443) = 3 ^ 8 * m + 6497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32443.1, data_15_32443.2]

/-- Complete interval computation for depth 15, residue 32444. -/
theorem bounds_15_32444 : exactInterval 15 32444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32444 : oddCount 32444 15 = 6 ∧ acceleratedOrbit 15 32444 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32444) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32444.1, data_15_32444.2]

/-- Complete interval computation for depth 15, residue 32445. -/
theorem bounds_15_32445 : exactInterval 15 32445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32445 : oddCount 32445 15 = 6 ∧ acceleratedOrbit 15 32445 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32445) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32445.1, data_15_32445.2]

/-- Complete interval computation for depth 15, residue 32446. -/
theorem bounds_15_32446 : exactInterval 15 32446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32446 : oddCount 32446 15 = 6 ∧ acceleratedOrbit 15 32446 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32446) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32446.1, data_15_32446.2]

/-- Complete interval computation for depth 15, residue 32447. -/
theorem bounds_15_32447 : exactInterval 15 32447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32447 : oddCount 32447 15 = 12 ∧ acceleratedOrbit 15 32447 = 526256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32447) = 3 ^ 12 * m + 526256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32447.1, data_15_32447.2]

/-- Complete interval computation for depth 15, residue 32448. -/
theorem bounds_15_32448 : exactInterval 15 32448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32448 : oddCount 32448 15 = 6 ∧ acceleratedOrbit 15 32448 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32448) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32448.1, data_15_32448.2]

/-- Complete interval computation for depth 15, residue 32449. -/
theorem bounds_15_32449 : exactInterval 15 32449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32449 : oddCount 32449 15 = 8 ∧ acceleratedOrbit 15 32449 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32449) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32449.1, data_15_32449.2]

/-- Complete interval computation for depth 15, residue 32450. -/
theorem bounds_15_32450 : exactInterval 15 32450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32450 : oddCount 32450 15 = 9 ∧ acceleratedOrbit 15 32450 = 19496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32450) = 3 ^ 9 * m + 19496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32450.1, data_15_32450.2]

/-- Complete interval computation for depth 15, residue 32451. -/
theorem bounds_15_32451 : exactInterval 15 32451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32451 : oddCount 32451 15 = 9 ∧ acceleratedOrbit 15 32451 = 19496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32451) = 3 ^ 9 * m + 19496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32451.1, data_15_32451.2]

/-- Complete interval computation for depth 15, residue 32452. -/
theorem bounds_15_32452 : exactInterval 15 32452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32452 : oddCount 32452 15 = 5 ∧ acceleratedOrbit 15 32452 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32452) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32452.1, data_15_32452.2]

/-- Complete interval computation for depth 15, residue 32453. -/
theorem bounds_15_32453 : exactInterval 15 32453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32453 : oddCount 32453 15 = 5 ∧ acceleratedOrbit 15 32453 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32453) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32453.1, data_15_32453.2]

/-- Complete interval computation for depth 15, residue 32454. -/
theorem bounds_15_32454 : exactInterval 15 32454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32454 : oddCount 32454 15 = 5 ∧ acceleratedOrbit 15 32454 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32454) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32454.1, data_15_32454.2]

/-- Complete interval computation for depth 15, residue 32455. -/
theorem bounds_15_32455 : exactInterval 15 32455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32455 : oddCount 32455 15 = 8 ∧ acceleratedOrbit 15 32455 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32455) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32455.1, data_15_32455.2]

/-- Complete interval computation for depth 15, residue 32456. -/
theorem bounds_15_32456 : exactInterval 15 32456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32456 : oddCount 32456 15 = 5 ∧ acceleratedOrbit 15 32456 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32456) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32456.1, data_15_32456.2]

/-- Complete interval computation for depth 15, residue 32457. -/
theorem bounds_15_32457 : exactInterval 15 32457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32457 : oddCount 32457 15 = 8 ∧ acceleratedOrbit 15 32457 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32457) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32457.1, data_15_32457.2]

/-- Complete interval computation for depth 15, residue 32458. -/
theorem bounds_15_32458 : exactInterval 15 32458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32458 : oddCount 32458 15 = 5 ∧ acceleratedOrbit 15 32458 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32458) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32458.1, data_15_32458.2]

/-- Complete interval computation for depth 15, residue 32459. -/
theorem bounds_15_32459 : exactInterval 15 32459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32459 : oddCount 32459 15 = 10 ∧ acceleratedOrbit 15 32459 = 58502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32459) = 3 ^ 10 * m + 58502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32459.1, data_15_32459.2]

/-- Complete interval computation for depth 15, residue 32460. -/
theorem bounds_15_32460 : exactInterval 15 32460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32460 : oddCount 32460 15 = 5 ∧ acceleratedOrbit 15 32460 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32460) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32460.1, data_15_32460.2]

/-- Complete interval computation for depth 15, residue 32461. -/
theorem bounds_15_32461 : exactInterval 15 32461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32461 : oddCount 32461 15 = 5 ∧ acceleratedOrbit 15 32461 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32461) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32461.1, data_15_32461.2]

/-- Complete interval computation for depth 15, residue 32462. -/
theorem bounds_15_32462 : exactInterval 15 32462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32462 : oddCount 32462 15 = 12 ∧ acceleratedOrbit 15 32462 = 526520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32462) = 3 ^ 12 * m + 526520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32462.1, data_15_32462.2]

/-- Complete interval computation for depth 15, residue 32463. -/
theorem bounds_15_32463 : exactInterval 15 32463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32463 : oddCount 32463 15 = 12 ∧ acceleratedOrbit 15 32463 = 526520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32463) = 3 ^ 12 * m + 526520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32463.1, data_15_32463.2]

/-- Complete interval computation for depth 15, residue 32464. -/
theorem bounds_15_32464 : exactInterval 15 32464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32464 : oddCount 32464 15 = 6 ∧ acceleratedOrbit 15 32464 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32464) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32464.1, data_15_32464.2]

/-- Complete interval computation for depth 15, residue 32465. -/
theorem bounds_15_32465 : exactInterval 15 32465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32465 : oddCount 32465 15 = 8 ∧ acceleratedOrbit 15 32465 = 6502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32465) = 3 ^ 8 * m + 6502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32465.1, data_15_32465.2]

/-- Complete interval computation for depth 15, residue 32466. -/
theorem bounds_15_32466 : exactInterval 15 32466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32466 : oddCount 32466 15 = 8 ∧ acceleratedOrbit 15 32466 = 6502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32466) = 3 ^ 8 * m + 6502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32466.1, data_15_32466.2]

/-- Complete interval computation for depth 15, residue 32467. -/
theorem bounds_15_32467 : exactInterval 15 32467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32467 : oddCount 32467 15 = 8 ∧ acceleratedOrbit 15 32467 = 6502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32467) = 3 ^ 8 * m + 6502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32467.1, data_15_32467.2]

/-- Complete interval computation for depth 15, residue 32468. -/
theorem bounds_15_32468 : exactInterval 15 32468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32468 : oddCount 32468 15 = 6 ∧ acceleratedOrbit 15 32468 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32468) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32468.1, data_15_32468.2]

/-- Complete interval computation for depth 15, residue 32469. -/
theorem bounds_15_32469 : exactInterval 15 32469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32469 : oddCount 32469 15 = 6 ∧ acceleratedOrbit 15 32469 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32469) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32469.1, data_15_32469.2]

/-- Complete interval computation for depth 15, residue 32470. -/
theorem bounds_15_32470 : exactInterval 15 32470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32470 : oddCount 32470 15 = 7 ∧ acceleratedOrbit 15 32470 = 2168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32470) = 3 ^ 7 * m + 2168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32470.1, data_15_32470.2]

/-- Complete interval computation for depth 15, residue 32471. -/
theorem bounds_15_32471 : exactInterval 15 32471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32471 : oddCount 32471 15 = 7 ∧ acceleratedOrbit 15 32471 = 2168 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32471) = 3 ^ 7 * m + 2168 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32471.1, data_15_32471.2]

/-- Complete interval computation for depth 15, residue 32472. -/
theorem bounds_15_32472 : exactInterval 15 32472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32472 : oddCount 32472 15 = 8 ∧ acceleratedOrbit 15 32472 = 6506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32472) = 3 ^ 8 * m + 6506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32472.1, data_15_32472.2]

end Collatz.Research.PassageAtlas.Batch0991
