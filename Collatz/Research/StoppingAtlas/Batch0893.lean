import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0893

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6533. -/
theorem bounds_13_6533 : exactInterval 13 6533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6533 : oddCount 6533 13 = 5 ∧ acceleratedOrbit 13 6533 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6533) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6533.1, data_13_6533.2]

/-- Complete interval computation for depth 13, residue 6534. -/
theorem bounds_13_6534 : exactInterval 13 6534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6534 : oddCount 6534 13 = 5 ∧ acceleratedOrbit 13 6534 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6534) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6534.1, data_13_6534.2]

/-- Complete interval computation for depth 13, residue 6535. -/
theorem bounds_13_6535 : exactInterval 13 6535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6535 : oddCount 6535 13 = 5 ∧ acceleratedOrbit 13 6535 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6535) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6535.1, data_13_6535.2]

/-- Complete interval computation for depth 13, residue 6536. -/
theorem bounds_13_6536 : exactInterval 13 6536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6536 : oddCount 6536 13 = 4 ∧ acceleratedOrbit 13 6536 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6536) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6536.1, data_13_6536.2]

/-- Complete interval computation for depth 13, residue 6537. -/
theorem bounds_13_6537 : exactInterval 13 6537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6537 : oddCount 6537 13 = 9 ∧ acceleratedOrbit 13 6537 = 15713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6537) = 3 ^ 9 * m + 15713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6537.1, data_13_6537.2]

/-- Complete interval computation for depth 13, residue 6538. -/
theorem bounds_13_6538 : exactInterval 13 6538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6538 : oddCount 6538 13 = 4 ∧ acceleratedOrbit 13 6538 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6538) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6538.1, data_13_6538.2]

/-- Complete interval computation for depth 13, residue 6539. -/
theorem bounds_13_6539 : exactInterval 13 6539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6539 : oddCount 6539 13 = 8 ∧ acceleratedOrbit 13 6539 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6539) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6539.1, data_13_6539.2]

/-- Complete interval computation for depth 13, residue 6540. -/
theorem bounds_13_6540 : exactInterval 13 6540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6540 : oddCount 6540 13 = 4 ∧ acceleratedOrbit 13 6540 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6540) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6540.1, data_13_6540.2]

/-- Complete interval computation for depth 13, residue 6541. -/
theorem bounds_13_6541 : exactInterval 13 6541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6541 : oddCount 6541 13 = 4 ∧ acceleratedOrbit 13 6541 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6541) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6541.1, data_13_6541.2]

/-- Complete interval computation for depth 13, residue 6542. -/
theorem bounds_13_6542 : exactInterval 13 6542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6542 : oddCount 6542 13 = 7 ∧ acceleratedOrbit 13 6542 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6542) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6542.1, data_13_6542.2]

/-- Complete interval computation for depth 13, residue 6543. -/
theorem bounds_13_6543 : exactInterval 13 6543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6543 : oddCount 6543 13 = 7 ∧ acceleratedOrbit 13 6543 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6543) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6543.1, data_13_6543.2]

/-- Complete interval computation for depth 13, residue 6544. -/
theorem bounds_13_6544 : exactInterval 13 6544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6544 : oddCount 6544 13 = 4 ∧ acceleratedOrbit 13 6544 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6544) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6544.1, data_13_6544.2]

/-- Complete interval computation for depth 13, residue 6545. -/
theorem bounds_13_6545 : exactInterval 13 6545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6545 : oddCount 6545 13 = 6 ∧ acceleratedOrbit 13 6545 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6545) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6545.1, data_13_6545.2]

/-- Complete interval computation for depth 13, residue 6546. -/
theorem bounds_13_6546 : exactInterval 13 6546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6546 : oddCount 6546 13 = 6 ∧ acceleratedOrbit 13 6546 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6546) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6546.1, data_13_6546.2]

/-- Complete interval computation for depth 13, residue 6547. -/
theorem bounds_13_6547 : exactInterval 13 6547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6547 : oddCount 6547 13 = 6 ∧ acceleratedOrbit 13 6547 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6547) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6547.1, data_13_6547.2]

end Collatz.Research.StoppingAtlas.Batch0893
