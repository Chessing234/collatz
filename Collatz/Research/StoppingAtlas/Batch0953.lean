import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0953

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7454. -/
theorem bounds_13_7454 : exactInterval 13 7454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7454 : oddCount 7454 13 = 7 ∧ acceleratedOrbit 13 7454 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7454) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7454.1, data_13_7454.2]

/-- Complete interval computation for depth 13, residue 7455. -/
theorem bounds_13_7455 : exactInterval 13 7455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7455) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7455 : oddCount 7455 13 = 7 ∧ acceleratedOrbit 13 7455 = 1991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7455) = 3 ^ 7 * m + 1991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7455.1, data_13_7455.2]

/-- Complete interval computation for depth 13, residue 7456. -/
theorem bounds_13_7456 : exactInterval 13 7456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7456 : oddCount 7456 13 = 6 ∧ acceleratedOrbit 13 7456 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7456) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7456.1, data_13_7456.2]

/-- Complete interval computation for depth 13, residue 7457. -/
theorem bounds_13_7457 : exactInterval 13 7457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7457 : oddCount 7457 13 = 6 ∧ acceleratedOrbit 13 7457 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7457) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7457.1, data_13_7457.2]

/-- Complete interval computation for depth 13, residue 7458. -/
theorem bounds_13_7458 : exactInterval 13 7458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7458 : oddCount 7458 13 = 6 ∧ acceleratedOrbit 13 7458 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7458) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7458.1, data_13_7458.2]

/-- Complete interval computation for depth 13, residue 7459. -/
theorem bounds_13_7459 : exactInterval 13 7459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7459 : oddCount 7459 13 = 6 ∧ acceleratedOrbit 13 7459 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7459) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7459.1, data_13_7459.2]

/-- Complete interval computation for depth 13, residue 7460. -/
theorem bounds_13_7460 : exactInterval 13 7460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7460 : oddCount 7460 13 = 6 ∧ acceleratedOrbit 13 7460 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7460) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7460.1, data_13_7460.2]

/-- Complete interval computation for depth 13, residue 7461. -/
theorem bounds_13_7461 : exactInterval 13 7461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7461 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7461) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7461 : oddCount 7461 13 = 6 ∧ acceleratedOrbit 13 7461 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7461 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7461) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7461.1, data_13_7461.2]

/-- Complete interval computation for depth 13, residue 7462. -/
theorem bounds_13_7462 : exactInterval 13 7462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7462 : oddCount 7462 13 = 6 ∧ acceleratedOrbit 13 7462 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7462) = 3 ^ 6 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7462.1, data_13_7462.2]

/-- Complete interval computation for depth 13, residue 7463. -/
theorem bounds_13_7463 : exactInterval 13 7463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7463 : oddCount 7463 13 = 7 ∧ acceleratedOrbit 13 7463 = 1993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7463) = 3 ^ 7 * m + 1993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7463.1, data_13_7463.2]

/-- Complete interval computation for depth 13, residue 7464. -/
theorem bounds_13_7464 : exactInterval 13 7464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7464 : oddCount 7464 13 = 6 ∧ acceleratedOrbit 13 7464 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7464) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7464.1, data_13_7464.2]

/-- Complete interval computation for depth 13, residue 7465. -/
theorem bounds_13_7465 : exactInterval 13 7465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7465 : oddCount 7465 13 = 9 ∧ acceleratedOrbit 13 7465 = 17941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7465) = 3 ^ 9 * m + 17941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7465.1, data_13_7465.2]

/-- Complete interval computation for depth 13, residue 7466. -/
theorem bounds_13_7466 : exactInterval 13 7466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7466 : oddCount 7466 13 = 6 ∧ acceleratedOrbit 13 7466 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7466) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7466.1, data_13_7466.2]

/-- Complete interval computation for depth 13, residue 7467. -/
theorem bounds_13_7467 : exactInterval 13 7467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7467 : oddCount 7467 13 = 8 ∧ acceleratedOrbit 13 7467 = 5984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7467) = 3 ^ 8 * m + 5984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7467.1, data_13_7467.2]

/-- Complete interval computation for depth 13, residue 7468. -/
theorem bounds_13_7468 : exactInterval 13 7468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7468 : oddCount 7468 13 = 4 ∧ acceleratedOrbit 13 7468 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7468) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7468.1, data_13_7468.2]

/-- Complete interval computation for depth 13, residue 7469. -/
theorem bounds_13_7469 : exactInterval 13 7469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7469 : oddCount 7469 13 = 4 ∧ acceleratedOrbit 13 7469 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7469) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7469.1, data_13_7469.2]

end Collatz.Research.StoppingAtlas.Batch0953
