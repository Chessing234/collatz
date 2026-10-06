import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0697

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3522. -/
theorem bounds_13_3522 : exactInterval 13 3522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3522 : oddCount 3522 13 = 8 ∧ acceleratedOrbit 13 3522 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3522) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3522.1, data_13_3522.2]

/-- Complete interval computation for depth 13, residue 3523. -/
theorem bounds_13_3523 : exactInterval 13 3523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3523 : oddCount 3523 13 = 8 ∧ acceleratedOrbit 13 3523 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3523) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3523.1, data_13_3523.2]

/-- Complete interval computation for depth 13, residue 3524. -/
theorem bounds_13_3524 : exactInterval 13 3524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3524 : oddCount 3524 13 = 5 ∧ acceleratedOrbit 13 3524 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3524) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3524.1, data_13_3524.2]

/-- Complete interval computation for depth 13, residue 3525. -/
theorem bounds_13_3525 : exactInterval 13 3525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3525 : oddCount 3525 13 = 5 ∧ acceleratedOrbit 13 3525 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3525) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3525.1, data_13_3525.2]

/-- Complete interval computation for depth 13, residue 3526. -/
theorem bounds_13_3526 : exactInterval 13 3526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3526 : oddCount 3526 13 = 5 ∧ acceleratedOrbit 13 3526 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3526) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3526.1, data_13_3526.2]

/-- Complete interval computation for depth 13, residue 3527. -/
theorem bounds_13_3527 : exactInterval 13 3527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3527 : oddCount 3527 13 = 6 ∧ acceleratedOrbit 13 3527 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3527) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3527.1, data_13_3527.2]

/-- Complete interval computation for depth 13, residue 3528. -/
theorem bounds_13_3528 : exactInterval 13 3528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3528 : oddCount 3528 13 = 4 ∧ acceleratedOrbit 13 3528 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3528) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3528.1, data_13_3528.2]

/-- Complete interval computation for depth 13, residue 3529. -/
theorem bounds_13_3529 : exactInterval 13 3529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3529 : oddCount 3529 13 = 7 ∧ acceleratedOrbit 13 3529 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3529) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3529.1, data_13_3529.2]

/-- Complete interval computation for depth 13, residue 3530. -/
theorem bounds_13_3530 : exactInterval 13 3530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3530 : oddCount 3530 13 = 4 ∧ acceleratedOrbit 13 3530 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3530) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3530.1, data_13_3530.2]

/-- Complete interval computation for depth 13, residue 3531. -/
theorem bounds_13_3531 : exactInterval 13 3531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3531 : oddCount 3531 13 = 8 ∧ acceleratedOrbit 13 3531 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3531) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3531.1, data_13_3531.2]

/-- Complete interval computation for depth 13, residue 3532. -/
theorem bounds_13_3532 : exactInterval 13 3532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3532 : oddCount 3532 13 = 4 ∧ acceleratedOrbit 13 3532 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3532) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3532.1, data_13_3532.2]

/-- Complete interval computation for depth 13, residue 3533. -/
theorem bounds_13_3533 : exactInterval 13 3533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3533 : oddCount 3533 13 = 4 ∧ acceleratedOrbit 13 3533 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3533) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3533.1, data_13_3533.2]

/-- Complete interval computation for depth 13, residue 3534. -/
theorem bounds_13_3534 : exactInterval 13 3534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3534 : oddCount 3534 13 = 9 ∧ acceleratedOrbit 13 3534 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3534) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3534.1, data_13_3534.2]

/-- Complete interval computation for depth 13, residue 3535. -/
theorem bounds_13_3535 : exactInterval 13 3535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3535 : oddCount 3535 13 = 9 ∧ acceleratedOrbit 13 3535 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3535) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3535.1, data_13_3535.2]

/-- Complete interval computation for depth 13, residue 3536. -/
theorem bounds_13_3536 : exactInterval 13 3536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3536 : oddCount 3536 13 = 5 ∧ acceleratedOrbit 13 3536 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3536) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3536.1, data_13_3536.2]

end Collatz.Research.StoppingAtlas.Batch0697
