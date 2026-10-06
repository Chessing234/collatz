import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0964

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31555. -/
theorem bounds_15_31555 : exactInterval 15 31555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31555 : oddCount 31555 15 = 8 ∧ acceleratedOrbit 15 31555 = 6320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31555) = 3 ^ 8 * m + 6320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31555.1, data_15_31555.2]

/-- Complete interval computation for depth 15, residue 31556. -/
theorem bounds_15_31556 : exactInterval 15 31556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31556 : oddCount 31556 15 = 7 ∧ acceleratedOrbit 15 31556 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31556) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31556.1, data_15_31556.2]

/-- Complete interval computation for depth 15, residue 31557. -/
theorem bounds_15_31557 : exactInterval 15 31557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31557 : oddCount 31557 15 = 7 ∧ acceleratedOrbit 15 31557 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31557) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31557.1, data_15_31557.2]

/-- Complete interval computation for depth 15, residue 31558. -/
theorem bounds_15_31558 : exactInterval 15 31558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31558 : oddCount 31558 15 = 7 ∧ acceleratedOrbit 15 31558 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31558) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31558.1, data_15_31558.2]

/-- Complete interval computation for depth 15, residue 31559. -/
theorem bounds_15_31559 : exactInterval 15 31559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31559 : oddCount 31559 15 = 9 ∧ acceleratedOrbit 15 31559 = 18958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31559) = 3 ^ 9 * m + 18958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31559.1, data_15_31559.2]

/-- Complete interval computation for depth 15, residue 31560. -/
theorem bounds_15_31560 : exactInterval 15 31560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31560 : oddCount 31560 15 = 7 ∧ acceleratedOrbit 15 31560 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31560) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31560.1, data_15_31560.2]

/-- Complete interval computation for depth 15, residue 31561. -/
theorem bounds_15_31561 : exactInterval 15 31561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31561 : oddCount 31561 15 = 7 ∧ acceleratedOrbit 15 31561 = 2107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31561) = 3 ^ 7 * m + 2107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31561.1, data_15_31561.2]

/-- Complete interval computation for depth 15, residue 31562. -/
theorem bounds_15_31562 : exactInterval 15 31562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31562 : oddCount 31562 15 = 7 ∧ acceleratedOrbit 15 31562 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31562) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31562.1, data_15_31562.2]

/-- Complete interval computation for depth 15, residue 31563. -/
theorem bounds_15_31563 : exactInterval 15 31563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31563 : oddCount 31563 15 = 7 ∧ acceleratedOrbit 15 31563 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31563) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31563.1, data_15_31563.2]

/-- Complete interval computation for depth 15, residue 31564. -/
theorem bounds_15_31564 : exactInterval 15 31564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31564 : oddCount 31564 15 = 7 ∧ acceleratedOrbit 15 31564 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31564) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31564.1, data_15_31564.2]

/-- Complete interval computation for depth 15, residue 31565. -/
theorem bounds_15_31565 : exactInterval 15 31565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31565 : oddCount 31565 15 = 7 ∧ acceleratedOrbit 15 31565 = 2108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31565) = 3 ^ 7 * m + 2108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31565.1, data_15_31565.2]

/-- Complete interval computation for depth 15, residue 31566. -/
theorem bounds_15_31566 : exactInterval 15 31566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31566 : oddCount 31566 15 = 7 ∧ acceleratedOrbit 15 31566 = 2107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31566) = 3 ^ 7 * m + 2107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31566.1, data_15_31566.2]

/-- Complete interval computation for depth 15, residue 31567. -/
theorem bounds_15_31567 : exactInterval 15 31567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31567 : oddCount 31567 15 = 7 ∧ acceleratedOrbit 15 31567 = 2107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31567) = 3 ^ 7 * m + 2107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31567.1, data_15_31567.2]

/-- Complete interval computation for depth 15, residue 31568. -/
theorem bounds_15_31568 : exactInterval 15 31568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31568 : oddCount 31568 15 = 5 ∧ acceleratedOrbit 15 31568 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31568) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31568.1, data_15_31568.2]

/-- Complete interval computation for depth 15, residue 31569. -/
theorem bounds_15_31569 : exactInterval 15 31569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31569 : oddCount 31569 15 = 8 ∧ acceleratedOrbit 15 31569 = 6322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31569) = 3 ^ 8 * m + 6322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31569.1, data_15_31569.2]

/-- Complete interval computation for depth 15, residue 31570. -/
theorem bounds_15_31570 : exactInterval 15 31570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31570 : oddCount 31570 15 = 8 ∧ acceleratedOrbit 15 31570 = 6322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31570) = 3 ^ 8 * m + 6322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31570.1, data_15_31570.2]

/-- Complete interval computation for depth 15, residue 31571. -/
theorem bounds_15_31571 : exactInterval 15 31571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31571 : oddCount 31571 15 = 8 ∧ acceleratedOrbit 15 31571 = 6322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31571) = 3 ^ 8 * m + 6322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31571.1, data_15_31571.2]

/-- Complete interval computation for depth 15, residue 31572. -/
theorem bounds_15_31572 : exactInterval 15 31572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31572 : oddCount 31572 15 = 5 ∧ acceleratedOrbit 15 31572 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31572) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31572.1, data_15_31572.2]

/-- Complete interval computation for depth 15, residue 31573. -/
theorem bounds_15_31573 : exactInterval 15 31573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31573 : oddCount 31573 15 = 5 ∧ acceleratedOrbit 15 31573 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31573) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31573.1, data_15_31573.2]

/-- Complete interval computation for depth 15, residue 31574. -/
theorem bounds_15_31574 : exactInterval 15 31574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31574 : oddCount 31574 15 = 8 ∧ acceleratedOrbit 15 31574 = 6323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31574) = 3 ^ 8 * m + 6323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31574.1, data_15_31574.2]

/-- Complete interval computation for depth 15, residue 31575. -/
theorem bounds_15_31575 : exactInterval 15 31575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31575 : oddCount 31575 15 = 8 ∧ acceleratedOrbit 15 31575 = 6323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31575) = 3 ^ 8 * m + 6323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31575.1, data_15_31575.2]

/-- Complete interval computation for depth 15, residue 31576. -/
theorem bounds_15_31576 : exactInterval 15 31576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31576 : oddCount 31576 15 = 6 ∧ acceleratedOrbit 15 31576 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31576) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31576.1, data_15_31576.2]

/-- Complete interval computation for depth 15, residue 31577. -/
theorem bounds_15_31577 : exactInterval 15 31577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31577 : oddCount 31577 15 = 6 ∧ acceleratedOrbit 15 31577 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31577) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31577.1, data_15_31577.2]

/-- Complete interval computation for depth 15, residue 31578. -/
theorem bounds_15_31578 : exactInterval 15 31578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31578 : oddCount 31578 15 = 6 ∧ acceleratedOrbit 15 31578 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31578) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31578.1, data_15_31578.2]

/-- Complete interval computation for depth 15, residue 31579. -/
theorem bounds_15_31579 : exactInterval 15 31579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31579 : oddCount 31579 15 = 9 ∧ acceleratedOrbit 15 31579 = 18971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31579) = 3 ^ 9 * m + 18971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31579.1, data_15_31579.2]

/-- Complete interval computation for depth 15, residue 31580. -/
theorem bounds_15_31580 : exactInterval 15 31580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31580 : oddCount 31580 15 = 6 ∧ acceleratedOrbit 15 31580 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31580) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31580.1, data_15_31580.2]

/-- Complete interval computation for depth 15, residue 31581. -/
theorem bounds_15_31581 : exactInterval 15 31581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31581 : oddCount 31581 15 = 6 ∧ acceleratedOrbit 15 31581 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31581) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31581.1, data_15_31581.2]

/-- Complete interval computation for depth 15, residue 31582. -/
theorem bounds_15_31582 : exactInterval 15 31582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31582 : oddCount 31582 15 = 9 ∧ acceleratedOrbit 15 31582 = 18974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31582) = 3 ^ 9 * m + 18974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31582.1, data_15_31582.2]

/-- Complete interval computation for depth 15, residue 31583. -/
theorem bounds_15_31583 : exactInterval 15 31583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31583 : oddCount 31583 15 = 9 ∧ acceleratedOrbit 15 31583 = 18974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31583) = 3 ^ 9 * m + 18974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31583.1, data_15_31583.2]

/-- Complete interval computation for depth 15, residue 31584. -/
theorem bounds_15_31584 : exactInterval 15 31584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31584 : oddCount 31584 15 = 6 ∧ acceleratedOrbit 15 31584 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31584) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31584.1, data_15_31584.2]

/-- Complete interval computation for depth 15, residue 31585. -/
theorem bounds_15_31585 : exactInterval 15 31585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31585 : oddCount 31585 15 = 11 ∧ acceleratedOrbit 15 31585 = 170768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31585) = 3 ^ 11 * m + 170768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31585.1, data_15_31585.2]

/-- Complete interval computation for depth 15, residue 31586. -/
theorem bounds_15_31586 : exactInterval 15 31586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31586 : oddCount 31586 15 = 6 ∧ acceleratedOrbit 15 31586 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31586) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31586.1, data_15_31586.2]

/-- Complete interval computation for depth 15, residue 31587. -/
theorem bounds_15_31587 : exactInterval 15 31587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31587 : oddCount 31587 15 = 6 ∧ acceleratedOrbit 15 31587 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31587) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31587.1, data_15_31587.2]

end Collatz.Research.PassageAtlas.Batch0964
