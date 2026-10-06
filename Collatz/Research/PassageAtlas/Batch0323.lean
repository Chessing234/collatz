import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0323

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10551. -/
theorem bounds_15_10551 : exactInterval 15 10551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10551 : oddCount 10551 15 = 8 ∧ acceleratedOrbit 15 10551 = 2113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10551) = 3 ^ 8 * m + 2113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10551.1, data_15_10551.2]

/-- Complete interval computation for depth 15, residue 10552. -/
theorem bounds_15_10552 : exactInterval 15 10552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10552 : oddCount 10552 15 = 6 ∧ acceleratedOrbit 15 10552 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10552) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10552.1, data_15_10552.2]

/-- Complete interval computation for depth 15, residue 10553. -/
theorem bounds_15_10553 : exactInterval 15 10553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10553 : oddCount 10553 15 = 8 ∧ acceleratedOrbit 15 10553 = 2114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10553) = 3 ^ 8 * m + 2114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10553.1, data_15_10553.2]

/-- Complete interval computation for depth 15, residue 10554. -/
theorem bounds_15_10554 : exactInterval 15 10554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10554 : oddCount 10554 15 = 6 ∧ acceleratedOrbit 15 10554 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10554) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10554.1, data_15_10554.2]

/-- Complete interval computation for depth 15, residue 10555. -/
theorem bounds_15_10555 : exactInterval 15 10555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10555 : oddCount 10555 15 = 6 ∧ acceleratedOrbit 15 10555 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10555) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10555.1, data_15_10555.2]

/-- Complete interval computation for depth 15, residue 10556. -/
theorem bounds_15_10556 : exactInterval 15 10556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10556 : oddCount 10556 15 = 6 ∧ acceleratedOrbit 15 10556 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10556) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10556.1, data_15_10556.2]

/-- Complete interval computation for depth 15, residue 10557. -/
theorem bounds_15_10557 : exactInterval 15 10557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10557 : oddCount 10557 15 = 6 ∧ acceleratedOrbit 15 10557 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10557) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10557.1, data_15_10557.2]

/-- Complete interval computation for depth 15, residue 10558. -/
theorem bounds_15_10558 : exactInterval 15 10558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10558 : oddCount 10558 15 = 10 ∧ acceleratedOrbit 15 10558 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10558) = 3 ^ 10 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10558.1, data_15_10558.2]

/-- Complete interval computation for depth 15, residue 10559. -/
theorem bounds_15_10559 : exactInterval 15 10559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10559 : oddCount 10559 15 = 10 ∧ acceleratedOrbit 15 10559 = 19030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10559) = 3 ^ 10 * m + 19030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10559.1, data_15_10559.2]

/-- Complete interval computation for depth 15, residue 10560. -/
theorem bounds_15_10560 : exactInterval 15 10560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10560 : oddCount 10560 15 = 6 ∧ acceleratedOrbit 15 10560 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10560) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10560.1, data_15_10560.2]

/-- Complete interval computation for depth 15, residue 10561. -/
theorem bounds_15_10561 : exactInterval 15 10561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10561 : oddCount 10561 15 = 6 ∧ acceleratedOrbit 15 10561 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10561) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10561.1, data_15_10561.2]

/-- Complete interval computation for depth 15, residue 10562. -/
theorem bounds_15_10562 : exactInterval 15 10562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10562 : oddCount 10562 15 = 8 ∧ acceleratedOrbit 15 10562 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10562) = 3 ^ 8 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10562.1, data_15_10562.2]

/-- Complete interval computation for depth 15, residue 10563. -/
theorem bounds_15_10563 : exactInterval 15 10563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10563 : oddCount 10563 15 = 8 ∧ acceleratedOrbit 15 10563 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10563) = 3 ^ 8 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10563.1, data_15_10563.2]

/-- Complete interval computation for depth 15, residue 10564. -/
theorem bounds_15_10564 : exactInterval 15 10564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10564 : oddCount 10564 15 = 8 ∧ acceleratedOrbit 15 10564 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10564) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10564.1, data_15_10564.2]

/-- Complete interval computation for depth 15, residue 10565. -/
theorem bounds_15_10565 : exactInterval 15 10565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10565 : oddCount 10565 15 = 8 ∧ acceleratedOrbit 15 10565 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10565) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10565.1, data_15_10565.2]

/-- Complete interval computation for depth 15, residue 10566. -/
theorem bounds_15_10566 : exactInterval 15 10566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10566 : oddCount 10566 15 = 8 ∧ acceleratedOrbit 15 10566 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10566) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10566.1, data_15_10566.2]

/-- Complete interval computation for depth 15, residue 10567. -/
theorem bounds_15_10567 : exactInterval 15 10567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10567 : oddCount 10567 15 = 10 ∧ acceleratedOrbit 15 10567 = 19045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10567) = 3 ^ 10 * m + 19045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10567.1, data_15_10567.2]

/-- Complete interval computation for depth 15, residue 10568. -/
theorem bounds_15_10568 : exactInterval 15 10568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10568 : oddCount 10568 15 = 8 ∧ acceleratedOrbit 15 10568 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10568) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10568.1, data_15_10568.2]

/-- Complete interval computation for depth 15, residue 10569. -/
theorem bounds_15_10569 : exactInterval 15 10569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10569 : oddCount 10569 15 = 8 ∧ acceleratedOrbit 15 10569 = 2117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10569) = 3 ^ 8 * m + 2117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10569.1, data_15_10569.2]

/-- Complete interval computation for depth 15, residue 10570. -/
theorem bounds_15_10570 : exactInterval 15 10570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10570 : oddCount 10570 15 = 8 ∧ acceleratedOrbit 15 10570 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10570) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10570.1, data_15_10570.2]

/-- Complete interval computation for depth 15, residue 10571. -/
theorem bounds_15_10571 : exactInterval 15 10571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10571 : oddCount 10571 15 = 8 ∧ acceleratedOrbit 15 10571 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10571) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10571.1, data_15_10571.2]

/-- Complete interval computation for depth 15, residue 10572. -/
theorem bounds_15_10572 : exactInterval 15 10572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10572 : oddCount 10572 15 = 8 ∧ acceleratedOrbit 15 10572 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10572) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10572.1, data_15_10572.2]

/-- Complete interval computation for depth 15, residue 10573. -/
theorem bounds_15_10573 : exactInterval 15 10573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10573 : oddCount 10573 15 = 8 ∧ acceleratedOrbit 15 10573 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10573) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10573.1, data_15_10573.2]

/-- Complete interval computation for depth 15, residue 10574. -/
theorem bounds_15_10574 : exactInterval 15 10574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10574 : oddCount 10574 15 = 10 ∧ acceleratedOrbit 15 10574 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10574) = 3 ^ 10 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10574.1, data_15_10574.2]

/-- Complete interval computation for depth 15, residue 10575. -/
theorem bounds_15_10575 : exactInterval 15 10575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10575 : oddCount 10575 15 = 10 ∧ acceleratedOrbit 15 10575 = 19061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10575) = 3 ^ 10 * m + 19061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10575.1, data_15_10575.2]

/-- Complete interval computation for depth 15, residue 10576. -/
theorem bounds_15_10576 : exactInterval 15 10576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10576 : oddCount 10576 15 = 6 ∧ acceleratedOrbit 15 10576 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10576) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10576.1, data_15_10576.2]

/-- Complete interval computation for depth 15, residue 10577. -/
theorem bounds_15_10577 : exactInterval 15 10577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10577 : oddCount 10577 15 = 9 ∧ acceleratedOrbit 15 10577 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10577) = 3 ^ 9 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10577.1, data_15_10577.2]

/-- Complete interval computation for depth 15, residue 10578. -/
theorem bounds_15_10578 : exactInterval 15 10578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10578 : oddCount 10578 15 = 9 ∧ acceleratedOrbit 15 10578 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10578) = 3 ^ 9 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10578.1, data_15_10578.2]

/-- Complete interval computation for depth 15, residue 10579. -/
theorem bounds_15_10579 : exactInterval 15 10579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10579 : oddCount 10579 15 = 9 ∧ acceleratedOrbit 15 10579 = 6356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10579) = 3 ^ 9 * m + 6356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10579.1, data_15_10579.2]

/-- Complete interval computation for depth 15, residue 10580. -/
theorem bounds_15_10580 : exactInterval 15 10580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10580 : oddCount 10580 15 = 6 ∧ acceleratedOrbit 15 10580 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10580) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10580.1, data_15_10580.2]

/-- Complete interval computation for depth 15, residue 10581. -/
theorem bounds_15_10581 : exactInterval 15 10581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10581 : oddCount 10581 15 = 6 ∧ acceleratedOrbit 15 10581 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10581) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10581.1, data_15_10581.2]

/-- Complete interval computation for depth 15, residue 10582. -/
theorem bounds_15_10582 : exactInterval 15 10582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10582 : oddCount 10582 15 = 6 ∧ acceleratedOrbit 15 10582 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10582) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10582.1, data_15_10582.2]

/-- Complete interval computation for depth 15, residue 10583. -/
theorem bounds_15_10583 : exactInterval 15 10583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10583 : oddCount 10583 15 = 6 ∧ acceleratedOrbit 15 10583 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10583) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10583.1, data_15_10583.2]

end Collatz.Research.PassageAtlas.Batch0323
