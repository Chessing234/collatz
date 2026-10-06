import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0834

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5626. -/
theorem bounds_13_5626 : exactInterval 13 5626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5626 : oddCount 5626 13 = 8 ∧ acceleratedOrbit 13 5626 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5626) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5626.1, data_13_5626.2]

/-- Complete interval computation for depth 13, residue 5627. -/
theorem bounds_13_5627 : exactInterval 13 5627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5627 : oddCount 5627 13 = 9 ∧ acceleratedOrbit 13 5627 = 13526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5627) = 3 ^ 9 * m + 13526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5627.1, data_13_5627.2]

/-- Complete interval computation for depth 13, residue 5628. -/
theorem bounds_13_5628 : exactInterval 13 5628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5628 : oddCount 5628 13 = 8 ∧ acceleratedOrbit 13 5628 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5628) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5628.1, data_13_5628.2]

/-- Complete interval computation for depth 13, residue 5629. -/
theorem bounds_13_5629 : exactInterval 13 5629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5629 : oddCount 5629 13 = 8 ∧ acceleratedOrbit 13 5629 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5629) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5629.1, data_13_5629.2]

/-- Complete interval computation for depth 13, residue 5630. -/
theorem bounds_13_5630 : exactInterval 13 5630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5630 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5630) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5630 : oddCount 5630 13 = 9 ∧ acceleratedOrbit 13 5630 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5630 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5630) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5630.1, data_13_5630.2]

/-- Complete interval computation for depth 13, residue 5631. -/
theorem bounds_13_5631 : exactInterval 13 5631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5631 : oddCount 5631 13 = 9 ∧ acceleratedOrbit 13 5631 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5631) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5631.1, data_13_5631.2]

/-- Complete interval computation for depth 13, residue 5632. -/
theorem bounds_13_5632 : exactInterval 13 5632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5632 : oddCount 5632 13 = 3 ∧ acceleratedOrbit 13 5632 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5632) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5632.1, data_13_5632.2]

/-- Complete interval computation for depth 13, residue 5633. -/
theorem bounds_13_5633 : exactInterval 13 5633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5633 : oddCount 5633 13 = 7 ∧ acceleratedOrbit 13 5633 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5633) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5633.1, data_13_5633.2]

/-- Complete interval computation for depth 13, residue 5634. -/
theorem bounds_13_5634 : exactInterval 13 5634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5634 : oddCount 5634 13 = 6 ∧ acceleratedOrbit 13 5634 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5634) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5634.1, data_13_5634.2]

/-- Complete interval computation for depth 13, residue 5635. -/
theorem bounds_13_5635 : exactInterval 13 5635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5635 : oddCount 5635 13 = 6 ∧ acceleratedOrbit 13 5635 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5635) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5635.1, data_13_5635.2]

/-- Complete interval computation for depth 13, residue 5636. -/
theorem bounds_13_5636 : exactInterval 13 5636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5636 : oddCount 5636 13 = 6 ∧ acceleratedOrbit 13 5636 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5636) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5636.1, data_13_5636.2]

/-- Complete interval computation for depth 13, residue 5637. -/
theorem bounds_13_5637 : exactInterval 13 5637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5637 : oddCount 5637 13 = 6 ∧ acceleratedOrbit 13 5637 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5637) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5637.1, data_13_5637.2]

/-- Complete interval computation for depth 13, residue 5638. -/
theorem bounds_13_5638 : exactInterval 13 5638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5638 : oddCount 5638 13 = 6 ∧ acceleratedOrbit 13 5638 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5638) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5638.1, data_13_5638.2]

/-- Complete interval computation for depth 13, residue 5639. -/
theorem bounds_13_5639 : exactInterval 13 5639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5639 : oddCount 5639 13 = 6 ∧ acceleratedOrbit 13 5639 = 502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5639) = 3 ^ 6 * m + 502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5639.1, data_13_5639.2]

/-- Complete interval computation for depth 13, residue 5640. -/
theorem bounds_13_5640 : exactInterval 13 5640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5640 : oddCount 5640 13 = 4 ∧ acceleratedOrbit 13 5640 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5640) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5640.1, data_13_5640.2]

/-- Complete interval computation for depth 13, residue 5641. -/
theorem bounds_13_5641 : exactInterval 13 5641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5641 : oddCount 5641 13 = 7 ∧ acceleratedOrbit 13 5641 = 1507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5641) = 3 ^ 7 * m + 1507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5641.1, data_13_5641.2]

end Collatz.Research.StoppingAtlas.Batch0834
