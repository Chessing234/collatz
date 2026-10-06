import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0765

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4567. -/
theorem bounds_13_4567 : exactInterval 13 4567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4567 : oddCount 4567 13 = 7 ∧ acceleratedOrbit 13 4567 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4567) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4567.1, data_13_4567.2]

/-- Complete interval computation for depth 13, residue 4568. -/
theorem bounds_13_4568 : exactInterval 13 4568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4568 : oddCount 4568 13 = 5 ∧ acceleratedOrbit 13 4568 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4568) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4568.1, data_13_4568.2]

/-- Complete interval computation for depth 13, residue 4569. -/
theorem bounds_13_4569 : exactInterval 13 4569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4569 : oddCount 4569 13 = 5 ∧ acceleratedOrbit 13 4569 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4569) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4569.1, data_13_4569.2]

/-- Complete interval computation for depth 13, residue 4570. -/
theorem bounds_13_4570 : exactInterval 13 4570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4570 : oddCount 4570 13 = 5 ∧ acceleratedOrbit 13 4570 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4570) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4570.1, data_13_4570.2]

/-- Complete interval computation for depth 13, residue 4571. -/
theorem bounds_13_4571 : exactInterval 13 4571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4571 : oddCount 4571 13 = 6 ∧ acceleratedOrbit 13 4571 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4571) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4571.1, data_13_4571.2]

/-- Complete interval computation for depth 13, residue 4572. -/
theorem bounds_13_4572 : exactInterval 13 4572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4572 : oddCount 4572 13 = 5 ∧ acceleratedOrbit 13 4572 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4572) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4572.1, data_13_4572.2]

/-- Complete interval computation for depth 13, residue 4573. -/
theorem bounds_13_4573 : exactInterval 13 4573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4573 : oddCount 4573 13 = 5 ∧ acceleratedOrbit 13 4573 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4573) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4573.1, data_13_4573.2]

/-- Complete interval computation for depth 13, residue 4574. -/
theorem bounds_13_4574 : exactInterval 13 4574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4574 : oddCount 4574 13 = 10 ∧ acceleratedOrbit 13 4574 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4574) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4574.1, data_13_4574.2]

/-- Complete interval computation for depth 13, residue 4575. -/
theorem bounds_13_4575 : exactInterval 13 4575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4575 : oddCount 4575 13 = 10 ∧ acceleratedOrbit 13 4575 = 32987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4575) = 3 ^ 10 * m + 32987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4575.1, data_13_4575.2]

/-- Complete interval computation for depth 13, residue 4576. -/
theorem bounds_13_4576 : exactInterval 13 4576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4576 : oddCount 4576 13 = 5 ∧ acceleratedOrbit 13 4576 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4576) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4576.1, data_13_4576.2]

/-- Complete interval computation for depth 13, residue 4577. -/
theorem bounds_13_4577 : exactInterval 13 4577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4577 : oddCount 4577 13 = 7 ∧ acceleratedOrbit 13 4577 = 1223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4577) = 3 ^ 7 * m + 1223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4577.1, data_13_4577.2]

/-- Complete interval computation for depth 13, residue 4578. -/
theorem bounds_13_4578 : exactInterval 13 4578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4578 : oddCount 4578 13 = 5 ∧ acceleratedOrbit 13 4578 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4578) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4578.1, data_13_4578.2]

/-- Complete interval computation for depth 13, residue 4579. -/
theorem bounds_13_4579 : exactInterval 13 4579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4579 : oddCount 4579 13 = 5 ∧ acceleratedOrbit 13 4579 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4579) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4579.1, data_13_4579.2]

/-- Complete interval computation for depth 13, residue 4580. -/
theorem bounds_13_4580 : exactInterval 13 4580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4580 : oddCount 4580 13 = 7 ∧ acceleratedOrbit 13 4580 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4580) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4580.1, data_13_4580.2]

/-- Complete interval computation for depth 13, residue 4581. -/
theorem bounds_13_4581 : exactInterval 13 4581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4581 : oddCount 4581 13 = 7 ∧ acceleratedOrbit 13 4581 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4581) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4581.1, data_13_4581.2]

end Collatz.Research.StoppingAtlas.Batch0765
