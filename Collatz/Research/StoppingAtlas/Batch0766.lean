import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0766

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4582. -/
theorem bounds_13_4582 : exactInterval 13 4582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4582 : oddCount 4582 13 = 7 ∧ acceleratedOrbit 13 4582 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4582) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4582.1, data_13_4582.2]

/-- Complete interval computation for depth 13, residue 4583. -/
theorem bounds_13_4583 : exactInterval 13 4583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4583 : oddCount 4583 13 = 10 ∧ acceleratedOrbit 13 4583 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4583) = 3 ^ 10 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4583.1, data_13_4583.2]

/-- Complete interval computation for depth 13, residue 4584. -/
theorem bounds_13_4584 : exactInterval 13 4584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4584 : oddCount 4584 13 = 5 ∧ acceleratedOrbit 13 4584 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4584) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4584.1, data_13_4584.2]

/-- Complete interval computation for depth 13, residue 4585. -/
theorem bounds_13_4585 : exactInterval 13 4585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4585 : oddCount 4585 13 = 8 ∧ acceleratedOrbit 13 4585 = 3674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4585) = 3 ^ 8 * m + 3674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4585.1, data_13_4585.2]

/-- Complete interval computation for depth 13, residue 4586. -/
theorem bounds_13_4586 : exactInterval 13 4586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4586 : oddCount 4586 13 = 5 ∧ acceleratedOrbit 13 4586 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4586) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4586.1, data_13_4586.2]

/-- Complete interval computation for depth 13, residue 4587. -/
theorem bounds_13_4587 : exactInterval 13 4587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4587 : oddCount 4587 13 = 9 ∧ acceleratedOrbit 13 4587 = 11026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4587) = 3 ^ 9 * m + 11026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4587.1, data_13_4587.2]

/-- Complete interval computation for depth 13, residue 4588. -/
theorem bounds_13_4588 : exactInterval 13 4588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4588 : oddCount 4588 13 = 6 ∧ acceleratedOrbit 13 4588 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4588) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4588.1, data_13_4588.2]

/-- Complete interval computation for depth 13, residue 4589. -/
theorem bounds_13_4589 : exactInterval 13 4589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4589 : oddCount 4589 13 = 6 ∧ acceleratedOrbit 13 4589 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4589) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4589.1, data_13_4589.2]

/-- Complete interval computation for depth 13, residue 4590. -/
theorem bounds_13_4590 : exactInterval 13 4590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4590 : oddCount 4590 13 = 6 ∧ acceleratedOrbit 13 4590 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4590) = 3 ^ 6 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4590.1, data_13_4590.2]

/-- Complete interval computation for depth 13, residue 4591. -/
theorem bounds_13_4591 : exactInterval 13 4591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4591 : oddCount 4591 13 = 11 ∧ acceleratedOrbit 13 4591 = 99305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4591) = 3 ^ 11 * m + 99305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4591.1, data_13_4591.2]

/-- Complete interval computation for depth 13, residue 4592. -/
theorem bounds_13_4592 : exactInterval 13 4592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4592 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4592) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4592 : oddCount 4592 13 = 6 ∧ acceleratedOrbit 13 4592 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4592 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4592) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4592.1, data_13_4592.2]

/-- Complete interval computation for depth 13, residue 4593. -/
theorem bounds_13_4593 : exactInterval 13 4593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4593 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4593) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4593 : oddCount 4593 13 = 5 ∧ acceleratedOrbit 13 4593 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4593 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4593) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4593.1, data_13_4593.2]

/-- Complete interval computation for depth 13, residue 4594. -/
theorem bounds_13_4594 : exactInterval 13 4594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4594 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4594) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4594 : oddCount 4594 13 = 7 ∧ acceleratedOrbit 13 4594 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4594 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4594) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4594.1, data_13_4594.2]

/-- Complete interval computation for depth 13, residue 4595. -/
theorem bounds_13_4595 : exactInterval 13 4595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4595 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4595) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4595 : oddCount 4595 13 = 7 ∧ acceleratedOrbit 13 4595 = 1228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4595 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4595) = 3 ^ 7 * m + 1228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4595.1, data_13_4595.2]

/-- Complete interval computation for depth 13, residue 4596. -/
theorem bounds_13_4596 : exactInterval 13 4596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4596 : oddCount 4596 13 = 6 ∧ acceleratedOrbit 13 4596 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4596) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4596.1, data_13_4596.2]

end Collatz.Research.StoppingAtlas.Batch0766
