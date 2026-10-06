import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0768

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4613. -/
theorem bounds_13_4613 : exactInterval 13 4613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4613 : oddCount 4613 13 = 7 ∧ acceleratedOrbit 13 4613 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4613) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4613.1, data_13_4613.2]

/-- Complete interval computation for depth 13, residue 4614. -/
theorem bounds_13_4614 : exactInterval 13 4614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4614 : oddCount 4614 13 = 7 ∧ acceleratedOrbit 13 4614 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4614) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4614.1, data_13_4614.2]

/-- Complete interval computation for depth 13, residue 4615. -/
theorem bounds_13_4615 : exactInterval 13 4615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4615 : oddCount 4615 13 = 9 ∧ acceleratedOrbit 13 4615 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4615) = 3 ^ 9 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4615.1, data_13_4615.2]

/-- Complete interval computation for depth 13, residue 4616. -/
theorem bounds_13_4616 : exactInterval 13 4616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4616 : oddCount 4616 13 = 4 ∧ acceleratedOrbit 13 4616 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4616) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4616.1, data_13_4616.2]

/-- Complete interval computation for depth 13, residue 4617. -/
theorem bounds_13_4617 : exactInterval 13 4617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4617 : oddCount 4617 13 = 5 ∧ acceleratedOrbit 13 4617 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4617) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4617.1, data_13_4617.2]

/-- Complete interval computation for depth 13, residue 4618. -/
theorem bounds_13_4618 : exactInterval 13 4618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4618 : oddCount 4618 13 = 4 ∧ acceleratedOrbit 13 4618 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4618) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4618.1, data_13_4618.2]

/-- Complete interval computation for depth 13, residue 4619. -/
theorem bounds_13_4619 : exactInterval 13 4619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4619 : oddCount 4619 13 = 7 ∧ acceleratedOrbit 13 4619 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4619) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4619.1, data_13_4619.2]

/-- Complete interval computation for depth 13, residue 4620. -/
theorem bounds_13_4620 : exactInterval 13 4620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4620 : oddCount 4620 13 = 4 ∧ acceleratedOrbit 13 4620 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4620) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4620.1, data_13_4620.2]

/-- Complete interval computation for depth 13, residue 4621. -/
theorem bounds_13_4621 : exactInterval 13 4621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4621 : oddCount 4621 13 = 4 ∧ acceleratedOrbit 13 4621 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4621) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4621.1, data_13_4621.2]

/-- Complete interval computation for depth 13, residue 4622. -/
theorem bounds_13_4622 : exactInterval 13 4622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4622 : oddCount 4622 13 = 7 ∧ acceleratedOrbit 13 4622 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4622) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4622.1, data_13_4622.2]

/-- Complete interval computation for depth 13, residue 4623. -/
theorem bounds_13_4623 : exactInterval 13 4623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4623 : oddCount 4623 13 = 7 ∧ acceleratedOrbit 13 4623 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4623) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4623.1, data_13_4623.2]

/-- Complete interval computation for depth 13, residue 4624. -/
theorem bounds_13_4624 : exactInterval 13 4624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4624 : oddCount 4624 13 = 4 ∧ acceleratedOrbit 13 4624 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4624) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4624.1, data_13_4624.2]

/-- Complete interval computation for depth 13, residue 4625. -/
theorem bounds_13_4625 : exactInterval 13 4625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4625 : oddCount 4625 13 = 4 ∧ acceleratedOrbit 13 4625 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4625) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4625.1, data_13_4625.2]

/-- Complete interval computation for depth 13, residue 4626. -/
theorem bounds_13_4626 : exactInterval 13 4626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4626 : oddCount 4626 13 = 6 ∧ acceleratedOrbit 13 4626 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4626) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4626.1, data_13_4626.2]

/-- Complete interval computation for depth 13, residue 4627. -/
theorem bounds_13_4627 : exactInterval 13 4627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4627 : oddCount 4627 13 = 6 ∧ acceleratedOrbit 13 4627 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4627) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4627.1, data_13_4627.2]

end Collatz.Research.StoppingAtlas.Batch0768
