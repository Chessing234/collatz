import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0201

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6553. -/
theorem bounds_15_6553 : exactInterval 15 6553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6553 : oddCount 6553 15 = 6 ∧ acceleratedOrbit 15 6553 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6553) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6553.1, data_15_6553.2]

/-- Complete interval computation for depth 15, residue 6554. -/
theorem bounds_15_6554 : exactInterval 15 6554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6554 : oddCount 6554 15 = 5 ∧ acceleratedOrbit 15 6554 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6554) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6554.1, data_15_6554.2]

/-- Complete interval computation for depth 15, residue 6555. -/
theorem bounds_15_6555 : exactInterval 15 6555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6555 : oddCount 6555 15 = 10 ∧ acceleratedOrbit 15 6555 = 11816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6555) = 3 ^ 10 * m + 11816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6555.1, data_15_6555.2]

/-- Complete interval computation for depth 15, residue 6556. -/
theorem bounds_15_6556 : exactInterval 15 6556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6556 : oddCount 6556 15 = 10 ∧ acceleratedOrbit 15 6556 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6556) = 3 ^ 10 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6556.1, data_15_6556.2]

/-- Complete interval computation for depth 15, residue 6557. -/
theorem bounds_15_6557 : exactInterval 15 6557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6557 : oddCount 6557 15 = 10 ∧ acceleratedOrbit 15 6557 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6557) = 3 ^ 10 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6557.1, data_15_6557.2]

/-- Complete interval computation for depth 15, residue 6558. -/
theorem bounds_15_6558 : exactInterval 15 6558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6558 : oddCount 6558 15 = 10 ∧ acceleratedOrbit 15 6558 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6558) = 3 ^ 10 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6558.1, data_15_6558.2]

/-- Complete interval computation for depth 15, residue 6559. -/
theorem bounds_15_6559 : exactInterval 15 6559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6559 : oddCount 6559 15 = 9 ∧ acceleratedOrbit 15 6559 = 3941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6559) = 3 ^ 9 * m + 3941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6559.1, data_15_6559.2]

/-- Complete interval computation for depth 15, residue 6560. -/
theorem bounds_15_6560 : exactInterval 15 6560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6560 : oddCount 6560 15 = 4 ∧ acceleratedOrbit 15 6560 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6560) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6560.1, data_15_6560.2]

/-- Complete interval computation for depth 15, residue 6561. -/
theorem bounds_15_6561 : exactInterval 15 6561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6561 : oddCount 6561 15 = 9 ∧ acceleratedOrbit 15 6561 = 3944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6561) = 3 ^ 9 * m + 3944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6561.1, data_15_6561.2]

/-- Complete interval computation for depth 15, residue 6562. -/
theorem bounds_15_6562 : exactInterval 15 6562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6562 : oddCount 6562 15 = 8 ∧ acceleratedOrbit 15 6562 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6562) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6562.1, data_15_6562.2]

/-- Complete interval computation for depth 15, residue 6563. -/
theorem bounds_15_6563 : exactInterval 15 6563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6563 : oddCount 6563 15 = 8 ∧ acceleratedOrbit 15 6563 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6563) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6563.1, data_15_6563.2]

/-- Complete interval computation for depth 15, residue 6564. -/
theorem bounds_15_6564 : exactInterval 15 6564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6564 : oddCount 6564 15 = 8 ∧ acceleratedOrbit 15 6564 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6564) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6564.1, data_15_6564.2]

/-- Complete interval computation for depth 15, residue 6565. -/
theorem bounds_15_6565 : exactInterval 15 6565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6565 : oddCount 6565 15 = 8 ∧ acceleratedOrbit 15 6565 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6565) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6565.1, data_15_6565.2]

/-- Complete interval computation for depth 15, residue 6566. -/
theorem bounds_15_6566 : exactInterval 15 6566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6566 : oddCount 6566 15 = 8 ∧ acceleratedOrbit 15 6566 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6566) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6566.1, data_15_6566.2]

/-- Complete interval computation for depth 15, residue 6567. -/
theorem bounds_15_6567 : exactInterval 15 6567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6567 : oddCount 6567 15 = 8 ∧ acceleratedOrbit 15 6567 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6567) = 3 ^ 8 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6567.1, data_15_6567.2]

/-- Complete interval computation for depth 15, residue 6568. -/
theorem bounds_15_6568 : exactInterval 15 6568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6568 : oddCount 6568 15 = 4 ∧ acceleratedOrbit 15 6568 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6568) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6568.1, data_15_6568.2]

/-- Complete interval computation for depth 15, residue 6569. -/
theorem bounds_15_6569 : exactInterval 15 6569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6569 : oddCount 6569 15 = 9 ∧ acceleratedOrbit 15 6569 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6569) = 3 ^ 9 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6569.1, data_15_6569.2]

/-- Complete interval computation for depth 15, residue 6570. -/
theorem bounds_15_6570 : exactInterval 15 6570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6570 : oddCount 6570 15 = 4 ∧ acceleratedOrbit 15 6570 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6570) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6570.1, data_15_6570.2]

/-- Complete interval computation for depth 15, residue 6571. -/
theorem bounds_15_6571 : exactInterval 15 6571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6571 : oddCount 6571 15 = 10 ∧ acceleratedOrbit 15 6571 = 11846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6571) = 3 ^ 10 * m + 11846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6571.1, data_15_6571.2]

/-- Complete interval computation for depth 15, residue 6572. -/
theorem bounds_15_6572 : exactInterval 15 6572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6572 : oddCount 6572 15 = 8 ∧ acceleratedOrbit 15 6572 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6572) = 3 ^ 8 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6572.1, data_15_6572.2]

/-- Complete interval computation for depth 15, residue 6573. -/
theorem bounds_15_6573 : exactInterval 15 6573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6573 : oddCount 6573 15 = 8 ∧ acceleratedOrbit 15 6573 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6573) = 3 ^ 8 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6573.1, data_15_6573.2]

/-- Complete interval computation for depth 15, residue 6574. -/
theorem bounds_15_6574 : exactInterval 15 6574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6574 : oddCount 6574 15 = 8 ∧ acceleratedOrbit 15 6574 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6574) = 3 ^ 8 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6574.1, data_15_6574.2]

/-- Complete interval computation for depth 15, residue 6575. -/
theorem bounds_15_6575 : exactInterval 15 6575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6575 : oddCount 6575 15 = 7 ∧ acceleratedOrbit 15 6575 = 439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6575) = 3 ^ 7 * m + 439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6575.1, data_15_6575.2]

/-- Complete interval computation for depth 15, residue 6576. -/
theorem bounds_15_6576 : exactInterval 15 6576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6576 : oddCount 6576 15 = 8 ∧ acceleratedOrbit 15 6576 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6576) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6576.1, data_15_6576.2]

/-- Complete interval computation for depth 15, residue 6577. -/
theorem bounds_15_6577 : exactInterval 15 6577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6577 : oddCount 6577 15 = 8 ∧ acceleratedOrbit 15 6577 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6577) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6577.1, data_15_6577.2]

/-- Complete interval computation for depth 15, residue 6578. -/
theorem bounds_15_6578 : exactInterval 15 6578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6578 : oddCount 6578 15 = 8 ∧ acceleratedOrbit 15 6578 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6578) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6578.1, data_15_6578.2]

/-- Complete interval computation for depth 15, residue 6579. -/
theorem bounds_15_6579 : exactInterval 15 6579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6579 : oddCount 6579 15 = 8 ∧ acceleratedOrbit 15 6579 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6579) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6579.1, data_15_6579.2]

/-- Complete interval computation for depth 15, residue 6580. -/
theorem bounds_15_6580 : exactInterval 15 6580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6580 : oddCount 6580 15 = 8 ∧ acceleratedOrbit 15 6580 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6580) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6580.1, data_15_6580.2]

/-- Complete interval computation for depth 15, residue 6581. -/
theorem bounds_15_6581 : exactInterval 15 6581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6581 : oddCount 6581 15 = 8 ∧ acceleratedOrbit 15 6581 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6581) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6581.1, data_15_6581.2]

/-- Complete interval computation for depth 15, residue 6582. -/
theorem bounds_15_6582 : exactInterval 15 6582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6582 : oddCount 6582 15 = 7 ∧ acceleratedOrbit 15 6582 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6582) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6582.1, data_15_6582.2]

/-- Complete interval computation for depth 15, residue 6583. -/
theorem bounds_15_6583 : exactInterval 15 6583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6583 : oddCount 6583 15 = 7 ∧ acceleratedOrbit 15 6583 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6583) = 3 ^ 7 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6583.1, data_15_6583.2]

/-- Complete interval computation for depth 15, residue 6584. -/
theorem bounds_15_6584 : exactInterval 15 6584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6584 : oddCount 6584 15 = 8 ∧ acceleratedOrbit 15 6584 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6584) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6584.1, data_15_6584.2]

/-- Complete interval computation for depth 15, residue 6585. -/
theorem bounds_15_6585 : exactInterval 15 6585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6585 : oddCount 6585 15 = 8 ∧ acceleratedOrbit 15 6585 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6585) = 3 ^ 8 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6585.1, data_15_6585.2]

end Collatz.Research.PassageAtlas.Batch0201
