import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0659

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21561. -/
theorem bounds_15_21561 : exactInterval 15 21561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21561 : oddCount 21561 15 = 8 ∧ acceleratedOrbit 15 21561 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21561) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21561.1, data_15_21561.2]

/-- Complete interval computation for depth 15, residue 21562. -/
theorem bounds_15_21562 : exactInterval 15 21562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21562 : oddCount 21562 15 = 5 ∧ acceleratedOrbit 15 21562 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21562) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21562.1, data_15_21562.2]

/-- Complete interval computation for depth 15, residue 21563. -/
theorem bounds_15_21563 : exactInterval 15 21563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21563 : oddCount 21563 15 = 9 ∧ acceleratedOrbit 15 21563 = 12955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21563) = 3 ^ 9 * m + 12955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21563.1, data_15_21563.2]

/-- Complete interval computation for depth 15, residue 21564. -/
theorem bounds_15_21564 : exactInterval 15 21564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21564 : oddCount 21564 15 = 5 ∧ acceleratedOrbit 15 21564 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21564) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21564.1, data_15_21564.2]

/-- Complete interval computation for depth 15, residue 21565. -/
theorem bounds_15_21565 : exactInterval 15 21565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21565 : oddCount 21565 15 = 5 ∧ acceleratedOrbit 15 21565 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21565) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21565.1, data_15_21565.2]

/-- Complete interval computation for depth 15, residue 21566. -/
theorem bounds_15_21566 : exactInterval 15 21566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21566 : oddCount 21566 15 = 8 ∧ acceleratedOrbit 15 21566 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21566) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21566.1, data_15_21566.2]

/-- Complete interval computation for depth 15, residue 21567. -/
theorem bounds_15_21567 : exactInterval 15 21567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21567 : oddCount 21567 15 = 8 ∧ acceleratedOrbit 15 21567 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21567) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21567.1, data_15_21567.2]

/-- Complete interval computation for depth 15, residue 21568. -/
theorem bounds_15_21568 : exactInterval 15 21568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21568 : oddCount 21568 15 = 6 ∧ acceleratedOrbit 15 21568 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21568) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21568.1, data_15_21568.2]

/-- Complete interval computation for depth 15, residue 21569. -/
theorem bounds_15_21569 : exactInterval 15 21569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21569 : oddCount 21569 15 = 5 ∧ acceleratedOrbit 15 21569 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21569) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21569.1, data_15_21569.2]

/-- Complete interval computation for depth 15, residue 21570. -/
theorem bounds_15_21570 : exactInterval 15 21570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21570 : oddCount 21570 15 = 5 ∧ acceleratedOrbit 15 21570 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21570) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21570.1, data_15_21570.2]

/-- Complete interval computation for depth 15, residue 21571. -/
theorem bounds_15_21571 : exactInterval 15 21571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21571 : oddCount 21571 15 = 5 ∧ acceleratedOrbit 15 21571 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21571) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21571.1, data_15_21571.2]

/-- Complete interval computation for depth 15, residue 21572. -/
theorem bounds_15_21572 : exactInterval 15 21572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21572 : oddCount 21572 15 = 6 ∧ acceleratedOrbit 15 21572 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21572) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21572.1, data_15_21572.2]

/-- Complete interval computation for depth 15, residue 21573. -/
theorem bounds_15_21573 : exactInterval 15 21573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21573 : oddCount 21573 15 = 6 ∧ acceleratedOrbit 15 21573 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21573) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21573.1, data_15_21573.2]

/-- Complete interval computation for depth 15, residue 21574. -/
theorem bounds_15_21574 : exactInterval 15 21574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21574 : oddCount 21574 15 = 6 ∧ acceleratedOrbit 15 21574 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21574) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21574.1, data_15_21574.2]

/-- Complete interval computation for depth 15, residue 21575. -/
theorem bounds_15_21575 : exactInterval 15 21575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21575 : oddCount 21575 15 = 9 ∧ acceleratedOrbit 15 21575 = 12961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21575) = 3 ^ 9 * m + 12961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21575.1, data_15_21575.2]

/-- Complete interval computation for depth 15, residue 21576. -/
theorem bounds_15_21576 : exactInterval 15 21576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21576 : oddCount 21576 15 = 7 ∧ acceleratedOrbit 15 21576 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21576) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21576.1, data_15_21576.2]

/-- Complete interval computation for depth 15, residue 21577. -/
theorem bounds_15_21577 : exactInterval 15 21577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21577 : oddCount 21577 15 = 8 ∧ acceleratedOrbit 15 21577 = 4321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21577) = 3 ^ 8 * m + 4321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21577.1, data_15_21577.2]

/-- Complete interval computation for depth 15, residue 21578. -/
theorem bounds_15_21578 : exactInterval 15 21578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21578 : oddCount 21578 15 = 7 ∧ acceleratedOrbit 15 21578 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21578) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21578.1, data_15_21578.2]

/-- Complete interval computation for depth 15, residue 21579. -/
theorem bounds_15_21579 : exactInterval 15 21579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21579 : oddCount 21579 15 = 6 ∧ acceleratedOrbit 15 21579 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21579) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21579.1, data_15_21579.2]

/-- Complete interval computation for depth 15, residue 21580. -/
theorem bounds_15_21580 : exactInterval 15 21580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21580 : oddCount 21580 15 = 7 ∧ acceleratedOrbit 15 21580 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21580) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21580.1, data_15_21580.2]

/-- Complete interval computation for depth 15, residue 21581. -/
theorem bounds_15_21581 : exactInterval 15 21581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21581 : oddCount 21581 15 = 7 ∧ acceleratedOrbit 15 21581 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21581) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21581.1, data_15_21581.2]

/-- Complete interval computation for depth 15, residue 21582. -/
theorem bounds_15_21582 : exactInterval 15 21582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21582 : oddCount 21582 15 = 7 ∧ acceleratedOrbit 15 21582 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21582) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21582.1, data_15_21582.2]

/-- Complete interval computation for depth 15, residue 21583. -/
theorem bounds_15_21583 : exactInterval 15 21583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21583 : oddCount 21583 15 = 7 ∧ acceleratedOrbit 15 21583 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21583) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21583.1, data_15_21583.2]

/-- Complete interval computation for depth 15, residue 21584. -/
theorem bounds_15_21584 : exactInterval 15 21584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21584 : oddCount 21584 15 = 6 ∧ acceleratedOrbit 15 21584 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21584) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21584.1, data_15_21584.2]

/-- Complete interval computation for depth 15, residue 21585. -/
theorem bounds_15_21585 : exactInterval 15 21585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21585 : oddCount 21585 15 = 7 ∧ acceleratedOrbit 15 21585 = 1441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21585) = 3 ^ 7 * m + 1441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21585.1, data_15_21585.2]

/-- Complete interval computation for depth 15, residue 21586. -/
theorem bounds_15_21586 : exactInterval 15 21586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21586 : oddCount 21586 15 = 10 ∧ acceleratedOrbit 15 21586 = 38906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21586) = 3 ^ 10 * m + 38906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21586.1, data_15_21586.2]

/-- Complete interval computation for depth 15, residue 21587. -/
theorem bounds_15_21587 : exactInterval 15 21587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21587 : oddCount 21587 15 = 10 ∧ acceleratedOrbit 15 21587 = 38906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21587) = 3 ^ 10 * m + 38906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21587.1, data_15_21587.2]

/-- Complete interval computation for depth 15, residue 21588. -/
theorem bounds_15_21588 : exactInterval 15 21588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21588 : oddCount 21588 15 = 6 ∧ acceleratedOrbit 15 21588 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21588) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21588.1, data_15_21588.2]

/-- Complete interval computation for depth 15, residue 21589. -/
theorem bounds_15_21589 : exactInterval 15 21589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21589 : oddCount 21589 15 = 6 ∧ acceleratedOrbit 15 21589 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21589) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21589.1, data_15_21589.2]

/-- Complete interval computation for depth 15, residue 21590. -/
theorem bounds_15_21590 : exactInterval 15 21590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21590 : oddCount 21590 15 = 6 ∧ acceleratedOrbit 15 21590 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21590) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21590.1, data_15_21590.2]

/-- Complete interval computation for depth 15, residue 21591. -/
theorem bounds_15_21591 : exactInterval 15 21591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21591 : oddCount 21591 15 = 6 ∧ acceleratedOrbit 15 21591 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21591) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21591.1, data_15_21591.2]

/-- Complete interval computation for depth 15, residue 21592. -/
theorem bounds_15_21592 : exactInterval 15 21592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21592 : oddCount 21592 15 = 6 ∧ acceleratedOrbit 15 21592 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21592) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21592.1, data_15_21592.2]

/-- Complete interval computation for depth 15, residue 21593. -/
theorem bounds_15_21593 : exactInterval 15 21593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21593 : oddCount 21593 15 = 7 ∧ acceleratedOrbit 15 21593 = 1442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21593) = 3 ^ 7 * m + 1442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21593.1, data_15_21593.2]

end Collatz.Research.PassageAtlas.Batch0659
