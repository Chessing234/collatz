import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0476

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15564. -/
theorem bounds_15_15564 : exactInterval 15 15564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15564 : oddCount 15564 15 = 5 ∧ acceleratedOrbit 15 15564 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15564) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15564.1, data_15_15564.2]

/-- Complete interval computation for depth 15, residue 15565. -/
theorem bounds_15_15565 : exactInterval 15 15565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15565 : oddCount 15565 15 = 5 ∧ acceleratedOrbit 15 15565 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15565) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15565.1, data_15_15565.2]

/-- Complete interval computation for depth 15, residue 15566. -/
theorem bounds_15_15566 : exactInterval 15 15566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15566 : oddCount 15566 15 = 9 ∧ acceleratedOrbit 15 15566 = 9352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15566) = 3 ^ 9 * m + 9352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15566.1, data_15_15566.2]

/-- Complete interval computation for depth 15, residue 15567. -/
theorem bounds_15_15567 : exactInterval 15 15567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15567 : oddCount 15567 15 = 9 ∧ acceleratedOrbit 15 15567 = 9352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15567) = 3 ^ 9 * m + 9352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15567.1, data_15_15567.2]

/-- Complete interval computation for depth 15, residue 15568. -/
theorem bounds_15_15568 : exactInterval 15 15568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15568 : oddCount 15568 15 = 6 ∧ acceleratedOrbit 15 15568 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15568) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15568.1, data_15_15568.2]

/-- Complete interval computation for depth 15, residue 15569. -/
theorem bounds_15_15569 : exactInterval 15 15569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15569 : oddCount 15569 15 = 10 ∧ acceleratedOrbit 15 15569 = 28066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15569) = 3 ^ 10 * m + 28066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15569.1, data_15_15569.2]

/-- Complete interval computation for depth 15, residue 15570. -/
theorem bounds_15_15570 : exactInterval 15 15570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15570 : oddCount 15570 15 = 10 ∧ acceleratedOrbit 15 15570 = 28066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15570) = 3 ^ 10 * m + 28066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15570.1, data_15_15570.2]

/-- Complete interval computation for depth 15, residue 15571. -/
theorem bounds_15_15571 : exactInterval 15 15571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15571 : oddCount 15571 15 = 10 ∧ acceleratedOrbit 15 15571 = 28066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15571) = 3 ^ 10 * m + 28066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15571.1, data_15_15571.2]

/-- Complete interval computation for depth 15, residue 15572. -/
theorem bounds_15_15572 : exactInterval 15 15572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15572 : oddCount 15572 15 = 6 ∧ acceleratedOrbit 15 15572 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15572) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15572.1, data_15_15572.2]

/-- Complete interval computation for depth 15, residue 15573. -/
theorem bounds_15_15573 : exactInterval 15 15573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15573 : oddCount 15573 15 = 6 ∧ acceleratedOrbit 15 15573 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15573) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15573.1, data_15_15573.2]

/-- Complete interval computation for depth 15, residue 15574. -/
theorem bounds_15_15574 : exactInterval 15 15574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15574 : oddCount 15574 15 = 9 ∧ acceleratedOrbit 15 15574 = 9359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15574) = 3 ^ 9 * m + 9359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15574.1, data_15_15574.2]

/-- Complete interval computation for depth 15, residue 15575. -/
theorem bounds_15_15575 : exactInterval 15 15575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15575 : oddCount 15575 15 = 9 ∧ acceleratedOrbit 15 15575 = 9359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15575) = 3 ^ 9 * m + 9359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15575.1, data_15_15575.2]

/-- Complete interval computation for depth 15, residue 15576. -/
theorem bounds_15_15576 : exactInterval 15 15576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15576 : oddCount 15576 15 = 8 ∧ acceleratedOrbit 15 15576 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15576) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15576.1, data_15_15576.2]

/-- Complete interval computation for depth 15, residue 15577. -/
theorem bounds_15_15577 : exactInterval 15 15577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15577 : oddCount 15577 15 = 8 ∧ acceleratedOrbit 15 15577 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15577) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15577.1, data_15_15577.2]

/-- Complete interval computation for depth 15, residue 15578. -/
theorem bounds_15_15578 : exactInterval 15 15578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15578 : oddCount 15578 15 = 8 ∧ acceleratedOrbit 15 15578 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15578) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15578.1, data_15_15578.2]

/-- Complete interval computation for depth 15, residue 15579. -/
theorem bounds_15_15579 : exactInterval 15 15579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15579 : oddCount 15579 15 = 7 ∧ acceleratedOrbit 15 15579 = 1040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15579) = 3 ^ 7 * m + 1040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15579.1, data_15_15579.2]

/-- Complete interval computation for depth 15, residue 15580. -/
theorem bounds_15_15580 : exactInterval 15 15580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15580 : oddCount 15580 15 = 8 ∧ acceleratedOrbit 15 15580 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15580) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15580.1, data_15_15580.2]

/-- Complete interval computation for depth 15, residue 15581. -/
theorem bounds_15_15581 : exactInterval 15 15581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15581 : oddCount 15581 15 = 8 ∧ acceleratedOrbit 15 15581 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15581) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15581.1, data_15_15581.2]

/-- Complete interval computation for depth 15, residue 15582. -/
theorem bounds_15_15582 : exactInterval 15 15582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15582 : oddCount 15582 15 = 9 ∧ acceleratedOrbit 15 15582 = 9362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15582) = 3 ^ 9 * m + 9362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15582.1, data_15_15582.2]

/-- Complete interval computation for depth 15, residue 15583. -/
theorem bounds_15_15583 : exactInterval 15 15583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15583 : oddCount 15583 15 = 9 ∧ acceleratedOrbit 15 15583 = 9362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15583) = 3 ^ 9 * m + 9362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15583.1, data_15_15583.2]

/-- Complete interval computation for depth 15, residue 15584. -/
theorem bounds_15_15584 : exactInterval 15 15584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15584 : oddCount 15584 15 = 7 ∧ acceleratedOrbit 15 15584 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15584) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15584.1, data_15_15584.2]

/-- Complete interval computation for depth 15, residue 15585. -/
theorem bounds_15_15585 : exactInterval 15 15585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15585 : oddCount 15585 15 = 8 ∧ acceleratedOrbit 15 15585 = 3121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15585) = 3 ^ 8 * m + 3121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15585.1, data_15_15585.2]

/-- Complete interval computation for depth 15, residue 15586. -/
theorem bounds_15_15586 : exactInterval 15 15586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15586 : oddCount 15586 15 = 6 ∧ acceleratedOrbit 15 15586 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15586) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15586.1, data_15_15586.2]

/-- Complete interval computation for depth 15, residue 15587. -/
theorem bounds_15_15587 : exactInterval 15 15587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15587 : oddCount 15587 15 = 6 ∧ acceleratedOrbit 15 15587 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15587) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15587.1, data_15_15587.2]

/-- Complete interval computation for depth 15, residue 15588. -/
theorem bounds_15_15588 : exactInterval 15 15588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15588 : oddCount 15588 15 = 6 ∧ acceleratedOrbit 15 15588 = 347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15588) = 3 ^ 6 * m + 347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15588.1, data_15_15588.2]

/-- Complete interval computation for depth 15, residue 15589. -/
theorem bounds_15_15589 : exactInterval 15 15589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15589 : oddCount 15589 15 = 6 ∧ acceleratedOrbit 15 15589 = 347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15589) = 3 ^ 6 * m + 347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15589.1, data_15_15589.2]

/-- Complete interval computation for depth 15, residue 15590. -/
theorem bounds_15_15590 : exactInterval 15 15590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15590 : oddCount 15590 15 = 6 ∧ acceleratedOrbit 15 15590 = 347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15590) = 3 ^ 6 * m + 347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15590.1, data_15_15590.2]

/-- Complete interval computation for depth 15, residue 15591. -/
theorem bounds_15_15591 : exactInterval 15 15591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15591 : oddCount 15591 15 = 8 ∧ acceleratedOrbit 15 15591 = 3122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15591) = 3 ^ 8 * m + 3122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15591.1, data_15_15591.2]

/-- Complete interval computation for depth 15, residue 15592. -/
theorem bounds_15_15592 : exactInterval 15 15592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15592 : oddCount 15592 15 = 7 ∧ acceleratedOrbit 15 15592 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15592) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15592.1, data_15_15592.2]

/-- Complete interval computation for depth 15, residue 15593. -/
theorem bounds_15_15593 : exactInterval 15 15593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15593 : oddCount 15593 15 = 10 ∧ acceleratedOrbit 15 15593 = 28106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15593) = 3 ^ 10 * m + 28106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15593.1, data_15_15593.2]

/-- Complete interval computation for depth 15, residue 15594. -/
theorem bounds_15_15594 : exactInterval 15 15594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15594 : oddCount 15594 15 = 7 ∧ acceleratedOrbit 15 15594 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15594) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15594.1, data_15_15594.2]

/-- Complete interval computation for depth 15, residue 15595. -/
theorem bounds_15_15595 : exactInterval 15 15595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15595 : oddCount 15595 15 = 12 ∧ acceleratedOrbit 15 15595 = 252962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15595) = 3 ^ 12 * m + 252962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15595.1, data_15_15595.2]

/-- Complete interval computation for depth 15, residue 15596. -/
theorem bounds_15_15596 : exactInterval 15 15596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15596 : oddCount 15596 15 = 7 ∧ acceleratedOrbit 15 15596 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15596) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15596.1, data_15_15596.2]

end Collatz.Research.PassageAtlas.Batch0476
