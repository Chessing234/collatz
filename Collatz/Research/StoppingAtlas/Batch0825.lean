import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0825

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5488. -/
theorem bounds_13_5488 : exactInterval 13 5488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5488 : oddCount 5488 13 = 5 ∧ acceleratedOrbit 13 5488 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5488) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5488.1, data_13_5488.2]

/-- Complete interval computation for depth 13, residue 5489. -/
theorem bounds_13_5489 : exactInterval 13 5489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5489 : oddCount 5489 13 = 5 ∧ acceleratedOrbit 13 5489 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5489) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5489.1, data_13_5489.2]

/-- Complete interval computation for depth 13, residue 5490. -/
theorem bounds_13_5490 : exactInterval 13 5490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5490 : oddCount 5490 13 = 5 ∧ acceleratedOrbit 13 5490 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5490) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5490.1, data_13_5490.2]

/-- Complete interval computation for depth 13, residue 5491. -/
theorem bounds_13_5491 : exactInterval 13 5491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5491 : oddCount 5491 13 = 5 ∧ acceleratedOrbit 13 5491 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5491) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5491.1, data_13_5491.2]

/-- Complete interval computation for depth 13, residue 5492. -/
theorem bounds_13_5492 : exactInterval 13 5492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5492 : oddCount 5492 13 = 5 ∧ acceleratedOrbit 13 5492 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5492) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5492.1, data_13_5492.2]

/-- Complete interval computation for depth 13, residue 5493. -/
theorem bounds_13_5493 : exactInterval 13 5493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5493 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5493) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5493 : oddCount 5493 13 = 5 ∧ acceleratedOrbit 13 5493 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5493 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5493) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5493.1, data_13_5493.2]

/-- Complete interval computation for depth 13, residue 5494. -/
theorem bounds_13_5494 : exactInterval 13 5494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5494 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5494) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5494 : oddCount 5494 13 = 7 ∧ acceleratedOrbit 13 5494 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5494 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5494) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5494.1, data_13_5494.2]

/-- Complete interval computation for depth 13, residue 5495. -/
theorem bounds_13_5495 : exactInterval 13 5495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5495 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5495) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5495 : oddCount 5495 13 = 7 ∧ acceleratedOrbit 13 5495 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5495 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5495) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5495.1, data_13_5495.2]

/-- Complete interval computation for depth 13, residue 5496. -/
theorem bounds_13_5496 : exactInterval 13 5496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5496 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5496) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5496 : oddCount 5496 13 = 6 ∧ acceleratedOrbit 13 5496 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5496 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5496) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5496.1, data_13_5496.2]

/-- Complete interval computation for depth 13, residue 5497. -/
theorem bounds_13_5497 : exactInterval 13 5497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5497 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5497) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5497 : oddCount 5497 13 = 9 ∧ acceleratedOrbit 13 5497 = 13213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5497 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5497) = 3 ^ 9 * m + 13213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5497.1, data_13_5497.2]

/-- Complete interval computation for depth 13, residue 5498. -/
theorem bounds_13_5498 : exactInterval 13 5498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5498 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5498) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5498 : oddCount 5498 13 = 6 ∧ acceleratedOrbit 13 5498 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5498 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5498) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5498.1, data_13_5498.2]

/-- Complete interval computation for depth 13, residue 5499. -/
theorem bounds_13_5499 : exactInterval 13 5499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5499 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5499) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5499 : oddCount 5499 13 = 7 ∧ acceleratedOrbit 13 5499 = 1469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5499 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5499) = 3 ^ 7 * m + 1469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5499.1, data_13_5499.2]

/-- Complete interval computation for depth 13, residue 5500. -/
theorem bounds_13_5500 : exactInterval 13 5500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5500 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5500) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5500 : oddCount 5500 13 = 6 ∧ acceleratedOrbit 13 5500 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5500 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5500) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5500.1, data_13_5500.2]

/-- Complete interval computation for depth 13, residue 5501. -/
theorem bounds_13_5501 : exactInterval 13 5501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5501 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5501) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5501 : oddCount 5501 13 = 6 ∧ acceleratedOrbit 13 5501 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5501 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5501) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5501.1, data_13_5501.2]

/-- Complete interval computation for depth 13, residue 5502. -/
theorem bounds_13_5502 : exactInterval 13 5502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5502 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5502) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5502 : oddCount 5502 13 = 9 ∧ acceleratedOrbit 13 5502 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5502 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5502) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5502.1, data_13_5502.2]

/-- Complete interval computation for depth 13, residue 5503. -/
theorem bounds_13_5503 : exactInterval 13 5503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5503 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5503) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5503 : oddCount 5503 13 = 9 ∧ acceleratedOrbit 13 5503 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5503 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5503) = 3 ^ 9 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5503.1, data_13_5503.2]

end Collatz.Research.StoppingAtlas.Batch0825
