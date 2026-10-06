import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0830

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5565. -/
theorem bounds_13_5565 : exactInterval 13 5565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5565 : oddCount 5565 13 = 7 ∧ acceleratedOrbit 13 5565 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5565) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5565.1, data_13_5565.2]

/-- Complete interval computation for depth 13, residue 5566. -/
theorem bounds_13_5566 : exactInterval 13 5566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5566 : oddCount 5566 13 = 7 ∧ acceleratedOrbit 13 5566 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5566) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5566.1, data_13_5566.2]

/-- Complete interval computation for depth 13, residue 5567. -/
theorem bounds_13_5567 : exactInterval 13 5567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5567 : oddCount 5567 13 = 11 ∧ acceleratedOrbit 13 5567 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5567) = 3 ^ 11 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5567.1, data_13_5567.2]

/-- Complete interval computation for depth 13, residue 5568. -/
theorem bounds_13_5568 : exactInterval 13 5568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5568 : oddCount 5568 13 = 4 ∧ acceleratedOrbit 13 5568 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5568) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5568.1, data_13_5568.2]

/-- Complete interval computation for depth 13, residue 5569. -/
theorem bounds_13_5569 : exactInterval 13 5569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5569 : oddCount 5569 13 = 6 ∧ acceleratedOrbit 13 5569 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5569) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5569.1, data_13_5569.2]

/-- Complete interval computation for depth 13, residue 5570. -/
theorem bounds_13_5570 : exactInterval 13 5570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5570 : oddCount 5570 13 = 8 ∧ acceleratedOrbit 13 5570 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5570) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5570.1, data_13_5570.2]

/-- Complete interval computation for depth 13, residue 5571. -/
theorem bounds_13_5571 : exactInterval 13 5571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5571 : oddCount 5571 13 = 8 ∧ acceleratedOrbit 13 5571 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5571) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5571.1, data_13_5571.2]

/-- Complete interval computation for depth 13, residue 5572. -/
theorem bounds_13_5572 : exactInterval 13 5572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5572 : oddCount 5572 13 = 4 ∧ acceleratedOrbit 13 5572 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5572) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5572.1, data_13_5572.2]

/-- Complete interval computation for depth 13, residue 5573. -/
theorem bounds_13_5573 : exactInterval 13 5573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5573 : oddCount 5573 13 = 4 ∧ acceleratedOrbit 13 5573 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5573) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5573.1, data_13_5573.2]

/-- Complete interval computation for depth 13, residue 5574. -/
theorem bounds_13_5574 : exactInterval 13 5574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5574 : oddCount 5574 13 = 4 ∧ acceleratedOrbit 13 5574 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5574) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5574.1, data_13_5574.2]

/-- Complete interval computation for depth 13, residue 5575. -/
theorem bounds_13_5575 : exactInterval 13 5575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5575 : oddCount 5575 13 = 7 ∧ acceleratedOrbit 13 5575 = 1489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5575) = 3 ^ 7 * m + 1489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5575.1, data_13_5575.2]

/-- Complete interval computation for depth 13, residue 5576. -/
theorem bounds_13_5576 : exactInterval 13 5576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5576 : oddCount 5576 13 = 5 ∧ acceleratedOrbit 13 5576 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5576) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5576.1, data_13_5576.2]

/-- Complete interval computation for depth 13, residue 5577. -/
theorem bounds_13_5577 : exactInterval 13 5577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5577 : oddCount 5577 13 = 6 ∧ acceleratedOrbit 13 5577 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5577) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5577.1, data_13_5577.2]

/-- Complete interval computation for depth 13, residue 5578. -/
theorem bounds_13_5578 : exactInterval 13 5578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5578 : oddCount 5578 13 = 5 ∧ acceleratedOrbit 13 5578 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5578) = 3 ^ 5 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5578.1, data_13_5578.2]

/-- Complete interval computation for depth 13, residue 5579. -/
theorem bounds_13_5579 : exactInterval 13 5579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5579 : oddCount 5579 13 = 6 ∧ acceleratedOrbit 13 5579 = 497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5579) = 3 ^ 6 * m + 497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5579.1, data_13_5579.2]

end Collatz.Research.StoppingAtlas.Batch0830
