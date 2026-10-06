import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0957

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7516. -/
theorem bounds_13_7516 : exactInterval 13 7516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7516 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7516) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7516 : oddCount 7516 13 = 6 ∧ acceleratedOrbit 13 7516 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7516 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7516) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7516.1, data_13_7516.2]

/-- Complete interval computation for depth 13, residue 7517. -/
theorem bounds_13_7517 : exactInterval 13 7517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7517 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7517) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7517 : oddCount 7517 13 = 6 ∧ acceleratedOrbit 13 7517 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7517 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7517) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7517.1, data_13_7517.2]

/-- Complete interval computation for depth 13, residue 7518. -/
theorem bounds_13_7518 : exactInterval 13 7518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7518 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7518) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7518 : oddCount 7518 13 = 7 ∧ acceleratedOrbit 13 7518 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7518 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7518) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7518.1, data_13_7518.2]

/-- Complete interval computation for depth 13, residue 7519. -/
theorem bounds_13_7519 : exactInterval 13 7519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7519 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7519) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7519 : oddCount 7519 13 = 7 ∧ acceleratedOrbit 13 7519 = 2008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7519 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7519) = 3 ^ 7 * m + 2008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7519.1, data_13_7519.2]

/-- Complete interval computation for depth 13, residue 7520. -/
theorem bounds_13_7520 : exactInterval 13 7520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7520 : oddCount 7520 13 = 6 ∧ acceleratedOrbit 13 7520 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7520) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7520.1, data_13_7520.2]

/-- Complete interval computation for depth 13, residue 7521. -/
theorem bounds_13_7521 : exactInterval 13 7521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7521 : oddCount 7521 13 = 7 ∧ acceleratedOrbit 13 7521 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7521) = 3 ^ 7 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7521.1, data_13_7521.2]

/-- Complete interval computation for depth 13, residue 7522. -/
theorem bounds_13_7522 : exactInterval 13 7522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7522 : oddCount 7522 13 = 5 ∧ acceleratedOrbit 13 7522 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7522) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7522.1, data_13_7522.2]

/-- Complete interval computation for depth 13, residue 7523. -/
theorem bounds_13_7523 : exactInterval 13 7523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7523 : oddCount 7523 13 = 5 ∧ acceleratedOrbit 13 7523 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7523) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7523.1, data_13_7523.2]

/-- Complete interval computation for depth 13, residue 7524. -/
theorem bounds_13_7524 : exactInterval 13 7524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7524 : oddCount 7524 13 = 5 ∧ acceleratedOrbit 13 7524 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7524) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7524.1, data_13_7524.2]

/-- Complete interval computation for depth 13, residue 7525. -/
theorem bounds_13_7525 : exactInterval 13 7525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7525 : oddCount 7525 13 = 5 ∧ acceleratedOrbit 13 7525 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7525) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7525.1, data_13_7525.2]

/-- Complete interval computation for depth 13, residue 7526. -/
theorem bounds_13_7526 : exactInterval 13 7526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7526 : oddCount 7526 13 = 5 ∧ acceleratedOrbit 13 7526 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7526) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7526.1, data_13_7526.2]

/-- Complete interval computation for depth 13, residue 7527. -/
theorem bounds_13_7527 : exactInterval 13 7527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7527 : oddCount 7527 13 = 10 ∧ acceleratedOrbit 13 7527 = 54265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7527) = 3 ^ 10 * m + 54265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7527.1, data_13_7527.2]

/-- Complete interval computation for depth 13, residue 7528. -/
theorem bounds_13_7528 : exactInterval 13 7528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7528 : oddCount 7528 13 = 6 ∧ acceleratedOrbit 13 7528 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7528) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7528.1, data_13_7528.2]

/-- Complete interval computation for depth 13, residue 7529. -/
theorem bounds_13_7529 : exactInterval 13 7529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7529 : oddCount 7529 13 = 7 ∧ acceleratedOrbit 13 7529 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7529) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7529.1, data_13_7529.2]

/-- Complete interval computation for depth 13, residue 7530. -/
theorem bounds_13_7530 : exactInterval 13 7530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7530 : oddCount 7530 13 = 6 ∧ acceleratedOrbit 13 7530 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7530) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7530.1, data_13_7530.2]

end Collatz.Research.StoppingAtlas.Batch0957
