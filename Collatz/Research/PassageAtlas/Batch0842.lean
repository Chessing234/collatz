import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0842

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27557. -/
theorem bounds_15_27557 : exactInterval 15 27557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27557 : oddCount 27557 15 = 8 ∧ acceleratedOrbit 15 27557 = 5519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27557) = 3 ^ 8 * m + 5519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27557.1, data_15_27557.2]

/-- Complete interval computation for depth 15, residue 27558. -/
theorem bounds_15_27558 : exactInterval 15 27558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27558 : oddCount 27558 15 = 8 ∧ acceleratedOrbit 15 27558 = 5519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27558) = 3 ^ 8 * m + 5519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27558.1, data_15_27558.2]

/-- Complete interval computation for depth 15, residue 27559. -/
theorem bounds_15_27559 : exactInterval 15 27559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27559 : oddCount 27559 15 = 10 ∧ acceleratedOrbit 15 27559 = 49666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27559) = 3 ^ 10 * m + 49666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27559.1, data_15_27559.2]

/-- Complete interval computation for depth 15, residue 27560. -/
theorem bounds_15_27560 : exactInterval 15 27560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27560 : oddCount 27560 15 = 5 ∧ acceleratedOrbit 15 27560 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27560) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27560.1, data_15_27560.2]

/-- Complete interval computation for depth 15, residue 27561. -/
theorem bounds_15_27561 : exactInterval 15 27561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27561 : oddCount 27561 15 = 10 ∧ acceleratedOrbit 15 27561 = 49670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27561) = 3 ^ 10 * m + 49670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27561.1, data_15_27561.2]

/-- Complete interval computation for depth 15, residue 27562. -/
theorem bounds_15_27562 : exactInterval 15 27562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27562 : oddCount 27562 15 = 5 ∧ acceleratedOrbit 15 27562 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27562) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27562.1, data_15_27562.2]

/-- Complete interval computation for depth 15, residue 27563. -/
theorem bounds_15_27563 : exactInterval 15 27563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27563 : oddCount 27563 15 = 7 ∧ acceleratedOrbit 15 27563 = 1840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27563) = 3 ^ 7 * m + 1840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27563.1, data_15_27563.2]

/-- Complete interval computation for depth 15, residue 27564. -/
theorem bounds_15_27564 : exactInterval 15 27564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27564 : oddCount 27564 15 = 8 ∧ acceleratedOrbit 15 27564 = 5521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27564) = 3 ^ 8 * m + 5521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27564.1, data_15_27564.2]

/-- Complete interval computation for depth 15, residue 27565. -/
theorem bounds_15_27565 : exactInterval 15 27565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27565 : oddCount 27565 15 = 8 ∧ acceleratedOrbit 15 27565 = 5521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27565) = 3 ^ 8 * m + 5521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27565.1, data_15_27565.2]

/-- Complete interval computation for depth 15, residue 27566. -/
theorem bounds_15_27566 : exactInterval 15 27566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27566 : oddCount 27566 15 = 8 ∧ acceleratedOrbit 15 27566 = 5521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27566) = 3 ^ 8 * m + 5521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27566.1, data_15_27566.2]

/-- Complete interval computation for depth 15, residue 27567. -/
theorem bounds_15_27567 : exactInterval 15 27567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27567 : oddCount 27567 15 = 8 ∧ acceleratedOrbit 15 27567 = 5521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27567) = 3 ^ 8 * m + 5521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27567.1, data_15_27567.2]

/-- Complete interval computation for depth 15, residue 27568. -/
theorem bounds_15_27568 : exactInterval 15 27568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27568 : oddCount 27568 15 = 6 ∧ acceleratedOrbit 15 27568 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27568) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27568.1, data_15_27568.2]

/-- Complete interval computation for depth 15, residue 27569. -/
theorem bounds_15_27569 : exactInterval 15 27569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27569 : oddCount 27569 15 = 6 ∧ acceleratedOrbit 15 27569 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27569) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27569.1, data_15_27569.2]

/-- Complete interval computation for depth 15, residue 27570. -/
theorem bounds_15_27570 : exactInterval 15 27570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27570 : oddCount 27570 15 = 6 ∧ acceleratedOrbit 15 27570 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27570) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27570.1, data_15_27570.2]

/-- Complete interval computation for depth 15, residue 27571. -/
theorem bounds_15_27571 : exactInterval 15 27571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27571 : oddCount 27571 15 = 6 ∧ acceleratedOrbit 15 27571 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27571) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27571.1, data_15_27571.2]

/-- Complete interval computation for depth 15, residue 27572. -/
theorem bounds_15_27572 : exactInterval 15 27572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27572 : oddCount 27572 15 = 6 ∧ acceleratedOrbit 15 27572 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27572) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27572.1, data_15_27572.2]

/-- Complete interval computation for depth 15, residue 27573. -/
theorem bounds_15_27573 : exactInterval 15 27573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27573 : oddCount 27573 15 = 6 ∧ acceleratedOrbit 15 27573 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27573) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27573.1, data_15_27573.2]

/-- Complete interval computation for depth 15, residue 27574. -/
theorem bounds_15_27574 : exactInterval 15 27574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27574 : oddCount 27574 15 = 6 ∧ acceleratedOrbit 15 27574 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27574) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27574.1, data_15_27574.2]

/-- Complete interval computation for depth 15, residue 27575. -/
theorem bounds_15_27575 : exactInterval 15 27575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27575 : oddCount 27575 15 = 6 ∧ acceleratedOrbit 15 27575 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27575) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27575.1, data_15_27575.2]

/-- Complete interval computation for depth 15, residue 27576. -/
theorem bounds_15_27576 : exactInterval 15 27576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27576 : oddCount 27576 15 = 6 ∧ acceleratedOrbit 15 27576 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27576) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27576.1, data_15_27576.2]

/-- Complete interval computation for depth 15, residue 27577. -/
theorem bounds_15_27577 : exactInterval 15 27577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27577 : oddCount 27577 15 = 7 ∧ acceleratedOrbit 15 27577 = 1841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27577) = 3 ^ 7 * m + 1841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27577.1, data_15_27577.2]

/-- Complete interval computation for depth 15, residue 27578. -/
theorem bounds_15_27578 : exactInterval 15 27578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27578 : oddCount 27578 15 = 6 ∧ acceleratedOrbit 15 27578 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27578) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27578.1, data_15_27578.2]

/-- Complete interval computation for depth 15, residue 27579. -/
theorem bounds_15_27579 : exactInterval 15 27579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27579 : oddCount 27579 15 = 7 ∧ acceleratedOrbit 15 27579 = 1841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27579) = 3 ^ 7 * m + 1841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27579.1, data_15_27579.2]

/-- Complete interval computation for depth 15, residue 27580. -/
theorem bounds_15_27580 : exactInterval 15 27580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27580 : oddCount 27580 15 = 10 ∧ acceleratedOrbit 15 27580 = 49709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27580) = 3 ^ 10 * m + 49709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27580.1, data_15_27580.2]

/-- Complete interval computation for depth 15, residue 27581. -/
theorem bounds_15_27581 : exactInterval 15 27581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27581 : oddCount 27581 15 = 10 ∧ acceleratedOrbit 15 27581 = 49709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27581) = 3 ^ 10 * m + 49709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27581.1, data_15_27581.2]

/-- Complete interval computation for depth 15, residue 27582. -/
theorem bounds_15_27582 : exactInterval 15 27582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27582 : oddCount 27582 15 = 10 ∧ acceleratedOrbit 15 27582 = 49709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27582) = 3 ^ 10 * m + 49709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27582.1, data_15_27582.2]

/-- Complete interval computation for depth 15, residue 27583. -/
theorem bounds_15_27583 : exactInterval 15 27583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27583 : oddCount 27583 15 = 11 ∧ acceleratedOrbit 15 27583 = 149123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27583) = 3 ^ 11 * m + 149123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27583.1, data_15_27583.2]

/-- Complete interval computation for depth 15, residue 27584. -/
theorem bounds_15_27584 : exactInterval 15 27584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27584 : oddCount 27584 15 = 5 ∧ acceleratedOrbit 15 27584 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27584) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27584.1, data_15_27584.2]

/-- Complete interval computation for depth 15, residue 27585. -/
theorem bounds_15_27585 : exactInterval 15 27585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27585 : oddCount 27585 15 = 8 ∧ acceleratedOrbit 15 27585 = 5525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27585) = 3 ^ 8 * m + 5525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27585.1, data_15_27585.2]

/-- Complete interval computation for depth 15, residue 27586. -/
theorem bounds_15_27586 : exactInterval 15 27586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27586 : oddCount 27586 15 = 8 ∧ acceleratedOrbit 15 27586 = 5525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27586) = 3 ^ 8 * m + 5525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27586.1, data_15_27586.2]

/-- Complete interval computation for depth 15, residue 27587. -/
theorem bounds_15_27587 : exactInterval 15 27587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27587 : oddCount 27587 15 = 8 ∧ acceleratedOrbit 15 27587 = 5525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27587) = 3 ^ 8 * m + 5525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27587.1, data_15_27587.2]

/-- Complete interval computation for depth 15, residue 27588. -/
theorem bounds_15_27588 : exactInterval 15 27588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27588 : oddCount 27588 15 = 5 ∧ acceleratedOrbit 15 27588 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27588) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27588.1, data_15_27588.2]

/-- Complete interval computation for depth 15, residue 27589. -/
theorem bounds_15_27589 : exactInterval 15 27589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27589 : oddCount 27589 15 = 5 ∧ acceleratedOrbit 15 27589 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27589) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27589.1, data_15_27589.2]

end Collatz.Research.PassageAtlas.Batch0842
