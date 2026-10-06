import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0506

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16547. -/
theorem bounds_15_16547 : exactInterval 15 16547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16547 : oddCount 16547 15 = 7 ∧ acceleratedOrbit 15 16547 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16547) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16547.1, data_15_16547.2]

/-- Complete interval computation for depth 15, residue 16548. -/
theorem bounds_15_16548 : exactInterval 15 16548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16548 : oddCount 16548 15 = 10 ∧ acceleratedOrbit 15 16548 = 29834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16548) = 3 ^ 10 * m + 29834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16548.1, data_15_16548.2]

/-- Complete interval computation for depth 15, residue 16549. -/
theorem bounds_15_16549 : exactInterval 15 16549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16549 : oddCount 16549 15 = 10 ∧ acceleratedOrbit 15 16549 = 29834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16549) = 3 ^ 10 * m + 29834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16549.1, data_15_16549.2]

/-- Complete interval computation for depth 15, residue 16550. -/
theorem bounds_15_16550 : exactInterval 15 16550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16550 : oddCount 16550 15 = 10 ∧ acceleratedOrbit 15 16550 = 29834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16550) = 3 ^ 10 * m + 29834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16550.1, data_15_16550.2]

/-- Complete interval computation for depth 15, residue 16551. -/
theorem bounds_15_16551 : exactInterval 15 16551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16551 : oddCount 16551 15 = 12 ∧ acceleratedOrbit 15 16551 = 268454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16551) = 3 ^ 12 * m + 268454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16551.1, data_15_16551.2]

/-- Complete interval computation for depth 15, residue 16552. -/
theorem bounds_15_16552 : exactInterval 15 16552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16552 : oddCount 16552 15 = 5 ∧ acceleratedOrbit 15 16552 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16552) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16552.1, data_15_16552.2]

/-- Complete interval computation for depth 15, residue 16553. -/
theorem bounds_15_16553 : exactInterval 15 16553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16553 : oddCount 16553 15 = 9 ∧ acceleratedOrbit 15 16553 = 9944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16553) = 3 ^ 9 * m + 9944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16553.1, data_15_16553.2]

/-- Complete interval computation for depth 15, residue 16554. -/
theorem bounds_15_16554 : exactInterval 15 16554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16554 : oddCount 16554 15 = 5 ∧ acceleratedOrbit 15 16554 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16554) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16554.1, data_15_16554.2]

/-- Complete interval computation for depth 15, residue 16555. -/
theorem bounds_15_16555 : exactInterval 15 16555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16555 : oddCount 16555 15 = 8 ∧ acceleratedOrbit 15 16555 = 3316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16555) = 3 ^ 8 * m + 3316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16555.1, data_15_16555.2]

/-- Complete interval computation for depth 15, residue 16556. -/
theorem bounds_15_16556 : exactInterval 15 16556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16556 : oddCount 16556 15 = 8 ∧ acceleratedOrbit 15 16556 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16556) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16556.1, data_15_16556.2]

/-- Complete interval computation for depth 15, residue 16557. -/
theorem bounds_15_16557 : exactInterval 15 16557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16557 : oddCount 16557 15 = 8 ∧ acceleratedOrbit 15 16557 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16557) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16557.1, data_15_16557.2]

/-- Complete interval computation for depth 15, residue 16558. -/
theorem bounds_15_16558 : exactInterval 15 16558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16558 : oddCount 16558 15 = 8 ∧ acceleratedOrbit 15 16558 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16558) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16558.1, data_15_16558.2]

/-- Complete interval computation for depth 15, residue 16559. -/
theorem bounds_15_16559 : exactInterval 15 16559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16559 : oddCount 16559 15 = 11 ∧ acceleratedOrbit 15 16559 = 89531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16559) = 3 ^ 11 * m + 89531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16559.1, data_15_16559.2]

/-- Complete interval computation for depth 15, residue 16560. -/
theorem bounds_15_16560 : exactInterval 15 16560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16560 : oddCount 16560 15 = 4 ∧ acceleratedOrbit 15 16560 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16560) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16560.1, data_15_16560.2]

/-- Complete interval computation for depth 15, residue 16561. -/
theorem bounds_15_16561 : exactInterval 15 16561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16561 : oddCount 16561 15 = 8 ∧ acceleratedOrbit 15 16561 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16561) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16561.1, data_15_16561.2]

/-- Complete interval computation for depth 15, residue 16562. -/
theorem bounds_15_16562 : exactInterval 15 16562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16562 : oddCount 16562 15 = 8 ∧ acceleratedOrbit 15 16562 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16562) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16562.1, data_15_16562.2]

/-- Complete interval computation for depth 15, residue 16563. -/
theorem bounds_15_16563 : exactInterval 15 16563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16563 : oddCount 16563 15 = 8 ∧ acceleratedOrbit 15 16563 = 3320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16563) = 3 ^ 8 * m + 3320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16563.1, data_15_16563.2]

/-- Complete interval computation for depth 15, residue 16564. -/
theorem bounds_15_16564 : exactInterval 15 16564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16564 : oddCount 16564 15 = 4 ∧ acceleratedOrbit 15 16564 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16564) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16564.1, data_15_16564.2]

/-- Complete interval computation for depth 15, residue 16565. -/
theorem bounds_15_16565 : exactInterval 15 16565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16565 : oddCount 16565 15 = 4 ∧ acceleratedOrbit 15 16565 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16565) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16565.1, data_15_16565.2]

/-- Complete interval computation for depth 15, residue 16566. -/
theorem bounds_15_16566 : exactInterval 15 16566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16566 : oddCount 16566 15 = 11 ∧ acceleratedOrbit 15 16566 = 89576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16566) = 3 ^ 11 * m + 89576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16566.1, data_15_16566.2]

/-- Complete interval computation for depth 15, residue 16567. -/
theorem bounds_15_16567 : exactInterval 15 16567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16567 : oddCount 16567 15 = 11 ∧ acceleratedOrbit 15 16567 = 89576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16567) = 3 ^ 11 * m + 89576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16567.1, data_15_16567.2]

/-- Complete interval computation for depth 15, residue 16568. -/
theorem bounds_15_16568 : exactInterval 15 16568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16568 : oddCount 16568 15 = 4 ∧ acceleratedOrbit 15 16568 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16568) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16568.1, data_15_16568.2]

/-- Complete interval computation for depth 15, residue 16569. -/
theorem bounds_15_16569 : exactInterval 15 16569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16569 : oddCount 16569 15 = 9 ∧ acceleratedOrbit 15 16569 = 9956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16569) = 3 ^ 9 * m + 9956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16569.1, data_15_16569.2]

/-- Complete interval computation for depth 15, residue 16570. -/
theorem bounds_15_16570 : exactInterval 15 16570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16570 : oddCount 16570 15 = 4 ∧ acceleratedOrbit 15 16570 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16570) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16570.1, data_15_16570.2]

/-- Complete interval computation for depth 15, residue 16571. -/
theorem bounds_15_16571 : exactInterval 15 16571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16571 : oddCount 16571 15 = 9 ∧ acceleratedOrbit 15 16571 = 9956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16571) = 3 ^ 9 * m + 9956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16571.1, data_15_16571.2]

/-- Complete interval computation for depth 15, residue 16572. -/
theorem bounds_15_16572 : exactInterval 15 16572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16572 : oddCount 16572 15 = 9 ∧ acceleratedOrbit 15 16572 = 9958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16572) = 3 ^ 9 * m + 9958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16572.1, data_15_16572.2]

/-- Complete interval computation for depth 15, residue 16573. -/
theorem bounds_15_16573 : exactInterval 15 16573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16573 : oddCount 16573 15 = 9 ∧ acceleratedOrbit 15 16573 = 9958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16573) = 3 ^ 9 * m + 9958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16573.1, data_15_16573.2]

/-- Complete interval computation for depth 15, residue 16574. -/
theorem bounds_15_16574 : exactInterval 15 16574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16574 : oddCount 16574 15 = 9 ∧ acceleratedOrbit 15 16574 = 9958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16574) = 3 ^ 9 * m + 9958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16574.1, data_15_16574.2]

/-- Complete interval computation for depth 15, residue 16575. -/
theorem bounds_15_16575 : exactInterval 15 16575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16575 : oddCount 16575 15 = 8 ∧ acceleratedOrbit 15 16575 = 3319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16575) = 3 ^ 8 * m + 3319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16575.1, data_15_16575.2]

/-- Complete interval computation for depth 15, residue 16576. -/
theorem bounds_15_16576 : exactInterval 15 16576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16576 : oddCount 16576 15 = 5 ∧ acceleratedOrbit 15 16576 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16576) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16576.1, data_15_16576.2]

/-- Complete interval computation for depth 15, residue 16577. -/
theorem bounds_15_16577 : exactInterval 15 16577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16577 : oddCount 16577 15 = 10 ∧ acceleratedOrbit 15 16577 = 29888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16577) = 3 ^ 10 * m + 29888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16577.1, data_15_16577.2]

/-- Complete interval computation for depth 15, residue 16578. -/
theorem bounds_15_16578 : exactInterval 15 16578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16578 : oddCount 16578 15 = 10 ∧ acceleratedOrbit 15 16578 = 29888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16578) = 3 ^ 10 * m + 29888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16578.1, data_15_16578.2]

/-- Complete interval computation for depth 15, residue 16579. -/
theorem bounds_15_16579 : exactInterval 15 16579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16579 : oddCount 16579 15 = 10 ∧ acceleratedOrbit 15 16579 = 29888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16579) = 3 ^ 10 * m + 29888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16579.1, data_15_16579.2]

end Collatz.Research.PassageAtlas.Batch0506
