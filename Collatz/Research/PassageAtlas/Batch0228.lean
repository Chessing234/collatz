import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0228

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7438. -/
theorem bounds_15_7438 : exactInterval 15 7438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7438 : oddCount 7438 15 = 7 ∧ acceleratedOrbit 15 7438 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7438) = 3 ^ 7 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7438.1, data_15_7438.2]

/-- Complete interval computation for depth 15, residue 7439. -/
theorem bounds_15_7439 : exactInterval 15 7439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7439 : oddCount 7439 15 = 7 ∧ acceleratedOrbit 15 7439 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7439) = 3 ^ 7 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7439.1, data_15_7439.2]

/-- Complete interval computation for depth 15, residue 7440. -/
theorem bounds_15_7440 : exactInterval 15 7440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7440 : oddCount 7440 15 = 5 ∧ acceleratedOrbit 15 7440 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7440) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7440.1, data_15_7440.2]

/-- Complete interval computation for depth 15, residue 7441. -/
theorem bounds_15_7441 : exactInterval 15 7441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7441 : oddCount 7441 15 = 6 ∧ acceleratedOrbit 15 7441 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7441) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7441.1, data_15_7441.2]

/-- Complete interval computation for depth 15, residue 7442. -/
theorem bounds_15_7442 : exactInterval 15 7442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7442 : oddCount 7442 15 = 11 ∧ acceleratedOrbit 15 7442 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7442) = 3 ^ 11 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7442.1, data_15_7442.2]

/-- Complete interval computation for depth 15, residue 7443. -/
theorem bounds_15_7443 : exactInterval 15 7443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7443 : oddCount 7443 15 = 11 ∧ acceleratedOrbit 15 7443 = 40256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7443) = 3 ^ 11 * m + 40256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7443.1, data_15_7443.2]

/-- Complete interval computation for depth 15, residue 7444. -/
theorem bounds_15_7444 : exactInterval 15 7444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7444 : oddCount 7444 15 = 5 ∧ acceleratedOrbit 15 7444 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7444) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7444.1, data_15_7444.2]

/-- Complete interval computation for depth 15, residue 7445. -/
theorem bounds_15_7445 : exactInterval 15 7445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7445 : oddCount 7445 15 = 5 ∧ acceleratedOrbit 15 7445 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7445) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7445.1, data_15_7445.2]

/-- Complete interval computation for depth 15, residue 7446. -/
theorem bounds_15_7446 : exactInterval 15 7446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7446 : oddCount 7446 15 = 6 ∧ acceleratedOrbit 15 7446 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7446) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7446.1, data_15_7446.2]

/-- Complete interval computation for depth 15, residue 7447. -/
theorem bounds_15_7447 : exactInterval 15 7447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7447 : oddCount 7447 15 = 6 ∧ acceleratedOrbit 15 7447 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7447) = 3 ^ 6 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7447.1, data_15_7447.2]

/-- Complete interval computation for depth 15, residue 7448. -/
theorem bounds_15_7448 : exactInterval 15 7448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7448 : oddCount 7448 15 = 5 ∧ acceleratedOrbit 15 7448 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7448) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7448.1, data_15_7448.2]

/-- Complete interval computation for depth 15, residue 7449. -/
theorem bounds_15_7449 : exactInterval 15 7449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7449 : oddCount 7449 15 = 9 ∧ acceleratedOrbit 15 7449 = 4477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7449) = 3 ^ 9 * m + 4477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7449.1, data_15_7449.2]

/-- Complete interval computation for depth 15, residue 7450. -/
theorem bounds_15_7450 : exactInterval 15 7450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7450 : oddCount 7450 15 = 5 ∧ acceleratedOrbit 15 7450 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7450) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7450.1, data_15_7450.2]

/-- Complete interval computation for depth 15, residue 7451. -/
theorem bounds_15_7451 : exactInterval 15 7451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7451 : oddCount 7451 15 = 10 ∧ acceleratedOrbit 15 7451 = 13430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7451) = 3 ^ 10 * m + 13430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7451.1, data_15_7451.2]

/-- Complete interval computation for depth 15, residue 7452. -/
theorem bounds_15_7452 : exactInterval 15 7452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7452 : oddCount 7452 15 = 9 ∧ acceleratedOrbit 15 7452 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7452) = 3 ^ 9 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7452.1, data_15_7452.2]

/-- Complete interval computation for depth 15, residue 7453. -/
theorem bounds_15_7453 : exactInterval 15 7453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7453 : oddCount 7453 15 = 9 ∧ acceleratedOrbit 15 7453 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7453) = 3 ^ 9 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7453.1, data_15_7453.2]

/-- Complete interval computation for depth 15, residue 7454. -/
theorem bounds_15_7454 : exactInterval 15 7454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7454 : oddCount 7454 15 = 9 ∧ acceleratedOrbit 15 7454 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7454) = 3 ^ 9 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7454.1, data_15_7454.2]

/-- Complete interval computation for depth 15, residue 7455. -/
theorem bounds_15_7455 : exactInterval 15 7455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7455 : oddCount 7455 15 = 9 ∧ acceleratedOrbit 15 7455 = 4481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7455) = 3 ^ 9 * m + 4481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7455.1, data_15_7455.2]

/-- Complete interval computation for depth 15, residue 7456. -/
theorem bounds_15_7456 : exactInterval 15 7456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7456 : oddCount 7456 15 = 6 ∧ acceleratedOrbit 15 7456 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7456) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7456.1, data_15_7456.2]

/-- Complete interval computation for depth 15, residue 7457. -/
theorem bounds_15_7457 : exactInterval 15 7457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7457 : oddCount 7457 15 = 7 ∧ acceleratedOrbit 15 7457 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7457) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7457.1, data_15_7457.2]

/-- Complete interval computation for depth 15, residue 7458. -/
theorem bounds_15_7458 : exactInterval 15 7458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7458 : oddCount 7458 15 = 7 ∧ acceleratedOrbit 15 7458 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7458) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7458.1, data_15_7458.2]

/-- Complete interval computation for depth 15, residue 7459. -/
theorem bounds_15_7459 : exactInterval 15 7459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7459 : oddCount 7459 15 = 7 ∧ acceleratedOrbit 15 7459 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7459) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7459.1, data_15_7459.2]

/-- Complete interval computation for depth 15, residue 7460. -/
theorem bounds_15_7460 : exactInterval 15 7460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7460 : oddCount 7460 15 = 7 ∧ acceleratedOrbit 15 7460 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7460) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7460.1, data_15_7460.2]

/-- Complete interval computation for depth 15, residue 7461. -/
theorem bounds_15_7461 : exactInterval 15 7461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7461 : oddCount 7461 15 = 7 ∧ acceleratedOrbit 15 7461 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7461) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7461.1, data_15_7461.2]

/-- Complete interval computation for depth 15, residue 7462. -/
theorem bounds_15_7462 : exactInterval 15 7462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7462 : oddCount 7462 15 = 7 ∧ acceleratedOrbit 15 7462 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7462) = 3 ^ 7 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7462.1, data_15_7462.2]

/-- Complete interval computation for depth 15, residue 7463. -/
theorem bounds_15_7463 : exactInterval 15 7463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7463 : oddCount 7463 15 = 8 ∧ acceleratedOrbit 15 7463 = 1495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7463) = 3 ^ 8 * m + 1495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7463.1, data_15_7463.2]

/-- Complete interval computation for depth 15, residue 7464. -/
theorem bounds_15_7464 : exactInterval 15 7464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7464 : oddCount 7464 15 = 6 ∧ acceleratedOrbit 15 7464 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7464) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7464.1, data_15_7464.2]

/-- Complete interval computation for depth 15, residue 7465. -/
theorem bounds_15_7465 : exactInterval 15 7465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7465 : oddCount 7465 15 = 10 ∧ acceleratedOrbit 15 7465 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7465) = 3 ^ 10 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7465.1, data_15_7465.2]

/-- Complete interval computation for depth 15, residue 7466. -/
theorem bounds_15_7466 : exactInterval 15 7466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7466 : oddCount 7466 15 = 6 ∧ acceleratedOrbit 15 7466 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7466) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7466.1, data_15_7466.2]

/-- Complete interval computation for depth 15, residue 7467. -/
theorem bounds_15_7467 : exactInterval 15 7467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7467 : oddCount 7467 15 = 8 ∧ acceleratedOrbit 15 7467 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7467) = 3 ^ 8 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7467.1, data_15_7467.2]

/-- Complete interval computation for depth 15, residue 7468. -/
theorem bounds_15_7468 : exactInterval 15 7468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7468 : oddCount 7468 15 = 5 ∧ acceleratedOrbit 15 7468 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7468) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7468.1, data_15_7468.2]

/-- Complete interval computation for depth 15, residue 7469. -/
theorem bounds_15_7469 : exactInterval 15 7469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7469 : oddCount 7469 15 = 5 ∧ acceleratedOrbit 15 7469 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7469) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7469.1, data_15_7469.2]

/-- Complete interval computation for depth 15, residue 7470. -/
theorem bounds_15_7470 : exactInterval 15 7470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7470 : oddCount 7470 15 = 5 ∧ acceleratedOrbit 15 7470 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7470) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7470.1, data_15_7470.2]

end Collatz.Research.PassageAtlas.Batch0228
