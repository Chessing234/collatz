import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0353

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11534. -/
theorem bounds_15_11534 : exactInterval 15 11534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11534 : oddCount 11534 15 = 8 ∧ acceleratedOrbit 15 11534 = 2312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11534) = 3 ^ 8 * m + 2312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11534.1, data_15_11534.2]

/-- Complete interval computation for depth 15, residue 11535. -/
theorem bounds_15_11535 : exactInterval 15 11535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11535 : oddCount 11535 15 = 8 ∧ acceleratedOrbit 15 11535 = 2312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11535) = 3 ^ 8 * m + 2312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11535.1, data_15_11535.2]

/-- Complete interval computation for depth 15, residue 11536. -/
theorem bounds_15_11536 : exactInterval 15 11536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11536 : oddCount 11536 15 = 5 ∧ acceleratedOrbit 15 11536 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11536) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11536.1, data_15_11536.2]

/-- Complete interval computation for depth 15, residue 11537. -/
theorem bounds_15_11537 : exactInterval 15 11537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11537 : oddCount 11537 15 = 6 ∧ acceleratedOrbit 15 11537 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11537) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11537.1, data_15_11537.2]

/-- Complete interval computation for depth 15, residue 11538. -/
theorem bounds_15_11538 : exactInterval 15 11538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11538 : oddCount 11538 15 = 8 ∧ acceleratedOrbit 15 11538 = 2311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11538) = 3 ^ 8 * m + 2311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11538.1, data_15_11538.2]

/-- Complete interval computation for depth 15, residue 11539. -/
theorem bounds_15_11539 : exactInterval 15 11539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11539 : oddCount 11539 15 = 8 ∧ acceleratedOrbit 15 11539 = 2311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11539) = 3 ^ 8 * m + 2311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11539.1, data_15_11539.2]

/-- Complete interval computation for depth 15, residue 11540. -/
theorem bounds_15_11540 : exactInterval 15 11540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11540 : oddCount 11540 15 = 5 ∧ acceleratedOrbit 15 11540 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11540) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11540.1, data_15_11540.2]

/-- Complete interval computation for depth 15, residue 11541. -/
theorem bounds_15_11541 : exactInterval 15 11541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11541 : oddCount 11541 15 = 5 ∧ acceleratedOrbit 15 11541 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11541) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11541.1, data_15_11541.2]

/-- Complete interval computation for depth 15, residue 11542. -/
theorem bounds_15_11542 : exactInterval 15 11542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11542 : oddCount 11542 15 = 6 ∧ acceleratedOrbit 15 11542 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11542) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11542.1, data_15_11542.2]

/-- Complete interval computation for depth 15, residue 11543. -/
theorem bounds_15_11543 : exactInterval 15 11543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11543 : oddCount 11543 15 = 6 ∧ acceleratedOrbit 15 11543 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11543) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11543.1, data_15_11543.2]

/-- Complete interval computation for depth 15, residue 11544. -/
theorem bounds_15_11544 : exactInterval 15 11544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11544 : oddCount 11544 15 = 5 ∧ acceleratedOrbit 15 11544 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11544) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11544.1, data_15_11544.2]

/-- Complete interval computation for depth 15, residue 11545. -/
theorem bounds_15_11545 : exactInterval 15 11545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11545 : oddCount 11545 15 = 9 ∧ acceleratedOrbit 15 11545 = 6938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11545) = 3 ^ 9 * m + 6938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11545.1, data_15_11545.2]

/-- Complete interval computation for depth 15, residue 11546. -/
theorem bounds_15_11546 : exactInterval 15 11546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11546 : oddCount 11546 15 = 5 ∧ acceleratedOrbit 15 11546 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11546) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11546.1, data_15_11546.2]

/-- Complete interval computation for depth 15, residue 11547. -/
theorem bounds_15_11547 : exactInterval 15 11547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11547 : oddCount 11547 15 = 12 ∧ acceleratedOrbit 15 11547 = 187298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11547) = 3 ^ 12 * m + 187298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11547.1, data_15_11547.2]

/-- Complete interval computation for depth 15, residue 11548. -/
theorem bounds_15_11548 : exactInterval 15 11548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11548 : oddCount 11548 15 = 9 ∧ acceleratedOrbit 15 11548 = 6941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11548) = 3 ^ 9 * m + 6941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11548.1, data_15_11548.2]

/-- Complete interval computation for depth 15, residue 11549. -/
theorem bounds_15_11549 : exactInterval 15 11549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11549 : oddCount 11549 15 = 9 ∧ acceleratedOrbit 15 11549 = 6941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11549) = 3 ^ 9 * m + 6941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11549.1, data_15_11549.2]

/-- Complete interval computation for depth 15, residue 11550. -/
theorem bounds_15_11550 : exactInterval 15 11550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11550 : oddCount 11550 15 = 9 ∧ acceleratedOrbit 15 11550 = 6941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11550) = 3 ^ 9 * m + 6941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11550.1, data_15_11550.2]

/-- Complete interval computation for depth 15, residue 11551. -/
theorem bounds_15_11551 : exactInterval 15 11551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11551 : oddCount 11551 15 = 6 ∧ acceleratedOrbit 15 11551 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11551) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11551.1, data_15_11551.2]

/-- Complete interval computation for depth 15, residue 11552. -/
theorem bounds_15_11552 : exactInterval 15 11552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11552 : oddCount 11552 15 = 5 ∧ acceleratedOrbit 15 11552 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11552) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11552.1, data_15_11552.2]

/-- Complete interval computation for depth 15, residue 11553. -/
theorem bounds_15_11553 : exactInterval 15 11553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11553 : oddCount 11553 15 = 7 ∧ acceleratedOrbit 15 11553 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11553) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11553.1, data_15_11553.2]

/-- Complete interval computation for depth 15, residue 11554. -/
theorem bounds_15_11554 : exactInterval 15 11554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11554 : oddCount 11554 15 = 7 ∧ acceleratedOrbit 15 11554 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11554) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11554.1, data_15_11554.2]

/-- Complete interval computation for depth 15, residue 11555. -/
theorem bounds_15_11555 : exactInterval 15 11555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11555 : oddCount 11555 15 = 7 ∧ acceleratedOrbit 15 11555 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11555) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11555.1, data_15_11555.2]

/-- Complete interval computation for depth 15, residue 11556. -/
theorem bounds_15_11556 : exactInterval 15 11556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11556 : oddCount 11556 15 = 7 ∧ acceleratedOrbit 15 11556 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11556) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11556.1, data_15_11556.2]

/-- Complete interval computation for depth 15, residue 11557. -/
theorem bounds_15_11557 : exactInterval 15 11557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11557 : oddCount 11557 15 = 7 ∧ acceleratedOrbit 15 11557 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11557) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11557.1, data_15_11557.2]

/-- Complete interval computation for depth 15, residue 11558. -/
theorem bounds_15_11558 : exactInterval 15 11558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11558 : oddCount 11558 15 = 7 ∧ acceleratedOrbit 15 11558 = 773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11558) = 3 ^ 7 * m + 773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11558.1, data_15_11558.2]

/-- Complete interval computation for depth 15, residue 11559. -/
theorem bounds_15_11559 : exactInterval 15 11559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11559 : oddCount 11559 15 = 8 ∧ acceleratedOrbit 15 11559 = 2315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11559) = 3 ^ 8 * m + 2315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11559.1, data_15_11559.2]

/-- Complete interval computation for depth 15, residue 11560. -/
theorem bounds_15_11560 : exactInterval 15 11560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11560 : oddCount 11560 15 = 5 ∧ acceleratedOrbit 15 11560 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11560) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11560.1, data_15_11560.2]

/-- Complete interval computation for depth 15, residue 11561. -/
theorem bounds_15_11561 : exactInterval 15 11561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11561 : oddCount 11561 15 = 10 ∧ acceleratedOrbit 15 11561 = 20837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11561) = 3 ^ 10 * m + 20837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11561.1, data_15_11561.2]

/-- Complete interval computation for depth 15, residue 11562. -/
theorem bounds_15_11562 : exactInterval 15 11562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11562 : oddCount 11562 15 = 5 ∧ acceleratedOrbit 15 11562 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11562) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11562.1, data_15_11562.2]

/-- Complete interval computation for depth 15, residue 11563. -/
theorem bounds_15_11563 : exactInterval 15 11563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11563 : oddCount 11563 15 = 7 ∧ acceleratedOrbit 15 11563 = 772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11563) = 3 ^ 7 * m + 772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11563.1, data_15_11563.2]

/-- Complete interval computation for depth 15, residue 11564. -/
theorem bounds_15_11564 : exactInterval 15 11564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11564 : oddCount 11564 15 = 5 ∧ acceleratedOrbit 15 11564 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11564) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11564.1, data_15_11564.2]

/-- Complete interval computation for depth 15, residue 11565. -/
theorem bounds_15_11565 : exactInterval 15 11565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11565 : oddCount 11565 15 = 5 ∧ acceleratedOrbit 15 11565 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11565) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11565.1, data_15_11565.2]

/-- Complete interval computation for depth 15, residue 11566. -/
theorem bounds_15_11566 : exactInterval 15 11566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11566 : oddCount 11566 15 = 5 ∧ acceleratedOrbit 15 11566 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11566) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11566.1, data_15_11566.2]

end Collatz.Research.PassageAtlas.Batch0353
