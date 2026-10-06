import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0890

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6487. -/
theorem bounds_13_6487 : exactInterval 13 6487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6487 : oddCount 6487 13 = 6 ∧ acceleratedOrbit 13 6487 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6487) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6487.1, data_13_6487.2]

/-- Complete interval computation for depth 13, residue 6488. -/
theorem bounds_13_6488 : exactInterval 13 6488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6488 : oddCount 6488 13 = 5 ∧ acceleratedOrbit 13 6488 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6488) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6488.1, data_13_6488.2]

/-- Complete interval computation for depth 13, residue 6489. -/
theorem bounds_13_6489 : exactInterval 13 6489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6489 : oddCount 6489 13 = 6 ∧ acceleratedOrbit 13 6489 = 578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6489) = 3 ^ 6 * m + 578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6489.1, data_13_6489.2]

/-- Complete interval computation for depth 13, residue 6490. -/
theorem bounds_13_6490 : exactInterval 13 6490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6490 : oddCount 6490 13 = 5 ∧ acceleratedOrbit 13 6490 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6490) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6490.1, data_13_6490.2]

/-- Complete interval computation for depth 13, residue 6491. -/
theorem bounds_13_6491 : exactInterval 13 6491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6491 : oddCount 6491 13 = 8 ∧ acceleratedOrbit 13 6491 = 5201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6491) = 3 ^ 8 * m + 5201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6491.1, data_13_6491.2]

/-- Complete interval computation for depth 13, residue 6492. -/
theorem bounds_13_6492 : exactInterval 13 6492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6492 : oddCount 6492 13 = 5 ∧ acceleratedOrbit 13 6492 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6492) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6492.1, data_13_6492.2]

/-- Complete interval computation for depth 13, residue 6493. -/
theorem bounds_13_6493 : exactInterval 13 6493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6493 : oddCount 6493 13 = 5 ∧ acceleratedOrbit 13 6493 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6493) = 3 ^ 5 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6493.1, data_13_6493.2]

/-- Complete interval computation for depth 13, residue 6494. -/
theorem bounds_13_6494 : exactInterval 13 6494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6494 : oddCount 6494 13 = 8 ∧ acceleratedOrbit 13 6494 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6494) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6494.1, data_13_6494.2]

/-- Complete interval computation for depth 13, residue 6495. -/
theorem bounds_13_6495 : exactInterval 13 6495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6495 : oddCount 6495 13 = 8 ∧ acceleratedOrbit 13 6495 = 5204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6495) = 3 ^ 8 * m + 5204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6495.1, data_13_6495.2]

/-- Complete interval computation for depth 13, residue 6496. -/
theorem bounds_13_6496 : exactInterval 13 6496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6496 : oddCount 6496 13 = 4 ∧ acceleratedOrbit 13 6496 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6496) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6496.1, data_13_6496.2]

/-- Complete interval computation for depth 13, residue 6497. -/
theorem bounds_13_6497 : exactInterval 13 6497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6497 : oddCount 6497 13 = 8 ∧ acceleratedOrbit 13 6497 = 5206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6497) = 3 ^ 8 * m + 5206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6497.1, data_13_6497.2]

/-- Complete interval computation for depth 13, residue 6498. -/
theorem bounds_13_6498 : exactInterval 13 6498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6498 : oddCount 6498 13 = 6 ∧ acceleratedOrbit 13 6498 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6498) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6498.1, data_13_6498.2]

/-- Complete interval computation for depth 13, residue 6499. -/
theorem bounds_13_6499 : exactInterval 13 6499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6499 : oddCount 6499 13 = 6 ∧ acceleratedOrbit 13 6499 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6499) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6499.1, data_13_6499.2]

/-- Complete interval computation for depth 13, residue 6500. -/
theorem bounds_13_6500 : exactInterval 13 6500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6500 : oddCount 6500 13 = 6 ∧ acceleratedOrbit 13 6500 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6500) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6500.1, data_13_6500.2]

/-- Complete interval computation for depth 13, residue 6501. -/
theorem bounds_13_6501 : exactInterval 13 6501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6501 : oddCount 6501 13 = 6 ∧ acceleratedOrbit 13 6501 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6501) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6501.1, data_13_6501.2]

end Collatz.Research.StoppingAtlas.Batch0890
