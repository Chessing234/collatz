import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0720

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23560. -/
theorem bounds_15_23560 : exactInterval 15 23560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23560 : oddCount 23560 15 = 8 ∧ acceleratedOrbit 15 23560 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23560) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23560.1, data_15_23560.2]

/-- Complete interval computation for depth 15, residue 23561. -/
theorem bounds_15_23561 : exactInterval 15 23561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23561 : oddCount 23561 15 = 10 ∧ acceleratedOrbit 15 23561 = 42464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23561) = 3 ^ 10 * m + 42464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23561.1, data_15_23561.2]

/-- Complete interval computation for depth 15, residue 23562. -/
theorem bounds_15_23562 : exactInterval 15 23562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23562 : oddCount 23562 15 = 8 ∧ acceleratedOrbit 15 23562 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23562) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23562.1, data_15_23562.2]

/-- Complete interval computation for depth 15, residue 23563. -/
theorem bounds_15_23563 : exactInterval 15 23563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23563 : oddCount 23563 15 = 5 ∧ acceleratedOrbit 15 23563 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23563) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23563.1, data_15_23563.2]

/-- Complete interval computation for depth 15, residue 23564. -/
theorem bounds_15_23564 : exactInterval 15 23564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23564 : oddCount 23564 15 = 8 ∧ acceleratedOrbit 15 23564 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23564) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23564.1, data_15_23564.2]

/-- Complete interval computation for depth 15, residue 23565. -/
theorem bounds_15_23565 : exactInterval 15 23565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23565 : oddCount 23565 15 = 8 ∧ acceleratedOrbit 15 23565 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23565) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23565.1, data_15_23565.2]

/-- Complete interval computation for depth 15, residue 23566. -/
theorem bounds_15_23566 : exactInterval 15 23566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23566 : oddCount 23566 15 = 8 ∧ acceleratedOrbit 15 23566 = 4720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23566) = 3 ^ 8 * m + 4720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23566.1, data_15_23566.2]

/-- Complete interval computation for depth 15, residue 23567. -/
theorem bounds_15_23567 : exactInterval 15 23567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23567 : oddCount 23567 15 = 8 ∧ acceleratedOrbit 15 23567 = 4720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23567) = 3 ^ 8 * m + 4720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23567.1, data_15_23567.2]

/-- Complete interval computation for depth 15, residue 23568. -/
theorem bounds_15_23568 : exactInterval 15 23568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23568 : oddCount 23568 15 = 6 ∧ acceleratedOrbit 15 23568 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23568) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23568.1, data_15_23568.2]

/-- Complete interval computation for depth 15, residue 23569. -/
theorem bounds_15_23569 : exactInterval 15 23569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23569 : oddCount 23569 15 = 8 ∧ acceleratedOrbit 15 23569 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23569) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23569.1, data_15_23569.2]

/-- Complete interval computation for depth 15, residue 23570. -/
theorem bounds_15_23570 : exactInterval 15 23570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23570 : oddCount 23570 15 = 7 ∧ acceleratedOrbit 15 23570 = 1574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23570) = 3 ^ 7 * m + 1574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23570.1, data_15_23570.2]

/-- Complete interval computation for depth 15, residue 23571. -/
theorem bounds_15_23571 : exactInterval 15 23571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23571 : oddCount 23571 15 = 7 ∧ acceleratedOrbit 15 23571 = 1574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23571) = 3 ^ 7 * m + 1574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23571.1, data_15_23571.2]

/-- Complete interval computation for depth 15, residue 23572. -/
theorem bounds_15_23572 : exactInterval 15 23572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23572 : oddCount 23572 15 = 6 ∧ acceleratedOrbit 15 23572 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23572) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23572.1, data_15_23572.2]

/-- Complete interval computation for depth 15, residue 23573. -/
theorem bounds_15_23573 : exactInterval 15 23573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23573 : oddCount 23573 15 = 6 ∧ acceleratedOrbit 15 23573 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23573) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23573.1, data_15_23573.2]

/-- Complete interval computation for depth 15, residue 23574. -/
theorem bounds_15_23574 : exactInterval 15 23574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23574 : oddCount 23574 15 = 8 ∧ acceleratedOrbit 15 23574 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23574) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23574.1, data_15_23574.2]

/-- Complete interval computation for depth 15, residue 23575. -/
theorem bounds_15_23575 : exactInterval 15 23575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23575 : oddCount 23575 15 = 8 ∧ acceleratedOrbit 15 23575 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23575) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23575.1, data_15_23575.2]

/-- Complete interval computation for depth 15, residue 23576. -/
theorem bounds_15_23576 : exactInterval 15 23576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23576 : oddCount 23576 15 = 6 ∧ acceleratedOrbit 15 23576 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23576) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23576.1, data_15_23576.2]

/-- Complete interval computation for depth 15, residue 23577. -/
theorem bounds_15_23577 : exactInterval 15 23577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23577 : oddCount 23577 15 = 9 ∧ acceleratedOrbit 15 23577 = 14165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23577) = 3 ^ 9 * m + 14165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23577.1, data_15_23577.2]

/-- Complete interval computation for depth 15, residue 23578. -/
theorem bounds_15_23578 : exactInterval 15 23578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23578 : oddCount 23578 15 = 6 ∧ acceleratedOrbit 15 23578 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23578) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23578.1, data_15_23578.2]

/-- Complete interval computation for depth 15, residue 23579. -/
theorem bounds_15_23579 : exactInterval 15 23579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23579 : oddCount 23579 15 = 10 ∧ acceleratedOrbit 15 23579 = 42493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23579) = 3 ^ 10 * m + 42493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23579.1, data_15_23579.2]

/-- Complete interval computation for depth 15, residue 23580. -/
theorem bounds_15_23580 : exactInterval 15 23580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23580 : oddCount 23580 15 = 8 ∧ acceleratedOrbit 15 23580 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23580) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23580.1, data_15_23580.2]

/-- Complete interval computation for depth 15, residue 23581. -/
theorem bounds_15_23581 : exactInterval 15 23581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23581 : oddCount 23581 15 = 8 ∧ acceleratedOrbit 15 23581 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23581) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23581.1, data_15_23581.2]

/-- Complete interval computation for depth 15, residue 23582. -/
theorem bounds_15_23582 : exactInterval 15 23582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23582 : oddCount 23582 15 = 8 ∧ acceleratedOrbit 15 23582 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23582) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23582.1, data_15_23582.2]

/-- Complete interval computation for depth 15, residue 23583. -/
theorem bounds_15_23583 : exactInterval 15 23583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23583 : oddCount 23583 15 = 10 ∧ acceleratedOrbit 15 23583 = 42500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23583) = 3 ^ 10 * m + 42500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23583.1, data_15_23583.2]

/-- Complete interval computation for depth 15, residue 23584. -/
theorem bounds_15_23584 : exactInterval 15 23584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23584 : oddCount 23584 15 = 7 ∧ acceleratedOrbit 15 23584 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23584) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23584.1, data_15_23584.2]

/-- Complete interval computation for depth 15, residue 23585. -/
theorem bounds_15_23585 : exactInterval 15 23585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23585 : oddCount 23585 15 = 9 ∧ acceleratedOrbit 15 23585 = 14170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23585) = 3 ^ 9 * m + 14170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23585.1, data_15_23585.2]

/-- Complete interval computation for depth 15, residue 23586. -/
theorem bounds_15_23586 : exactInterval 15 23586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23586 : oddCount 23586 15 = 6 ∧ acceleratedOrbit 15 23586 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23586) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23586.1, data_15_23586.2]

/-- Complete interval computation for depth 15, residue 23587. -/
theorem bounds_15_23587 : exactInterval 15 23587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23587 : oddCount 23587 15 = 6 ∧ acceleratedOrbit 15 23587 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23587) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23587.1, data_15_23587.2]

/-- Complete interval computation for depth 15, residue 23588. -/
theorem bounds_15_23588 : exactInterval 15 23588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23588 : oddCount 23588 15 = 10 ∧ acceleratedOrbit 15 23588 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23588) = 3 ^ 10 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23588.1, data_15_23588.2]

/-- Complete interval computation for depth 15, residue 23589. -/
theorem bounds_15_23589 : exactInterval 15 23589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23589 : oddCount 23589 15 = 10 ∧ acceleratedOrbit 15 23589 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23589) = 3 ^ 10 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23589.1, data_15_23589.2]

/-- Complete interval computation for depth 15, residue 23590. -/
theorem bounds_15_23590 : exactInterval 15 23590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23590 : oddCount 23590 15 = 10 ∧ acceleratedOrbit 15 23590 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23590) = 3 ^ 10 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23590.1, data_15_23590.2]

/-- Complete interval computation for depth 15, residue 23591. -/
theorem bounds_15_23591 : exactInterval 15 23591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23591 : oddCount 23591 15 = 9 ∧ acceleratedOrbit 15 23591 = 14174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23591) = 3 ^ 9 * m + 14174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23591.1, data_15_23591.2]

end Collatz.Research.PassageAtlas.Batch0720
