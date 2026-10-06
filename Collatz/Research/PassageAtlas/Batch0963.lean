import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0963

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31522. -/
theorem bounds_15_31522 : exactInterval 15 31522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31522 : oddCount 31522 15 = 8 ∧ acceleratedOrbit 15 31522 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31522) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31522.1, data_15_31522.2]

/-- Complete interval computation for depth 15, residue 31523. -/
theorem bounds_15_31523 : exactInterval 15 31523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31523 : oddCount 31523 15 = 8 ∧ acceleratedOrbit 15 31523 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31523) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31523.1, data_15_31523.2]

/-- Complete interval computation for depth 15, residue 31524. -/
theorem bounds_15_31524 : exactInterval 15 31524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31524 : oddCount 31524 15 = 8 ∧ acceleratedOrbit 15 31524 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31524) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31524.1, data_15_31524.2]

/-- Complete interval computation for depth 15, residue 31525. -/
theorem bounds_15_31525 : exactInterval 15 31525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31525 : oddCount 31525 15 = 8 ∧ acceleratedOrbit 15 31525 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31525) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31525.1, data_15_31525.2]

/-- Complete interval computation for depth 15, residue 31526. -/
theorem bounds_15_31526 : exactInterval 15 31526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31526 : oddCount 31526 15 = 8 ∧ acceleratedOrbit 15 31526 = 6317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31526) = 3 ^ 8 * m + 6317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31526.1, data_15_31526.2]

/-- Complete interval computation for depth 15, residue 31527. -/
theorem bounds_15_31527 : exactInterval 15 31527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31527 : oddCount 31527 15 = 11 ∧ acceleratedOrbit 15 31527 = 170450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31527) = 3 ^ 11 * m + 170450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31527.1, data_15_31527.2]

/-- Complete interval computation for depth 15, residue 31528. -/
theorem bounds_15_31528 : exactInterval 15 31528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31528 : oddCount 31528 15 = 3 ∧ acceleratedOrbit 15 31528 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31528) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31528.1, data_15_31528.2]

/-- Complete interval computation for depth 15, residue 31529. -/
theorem bounds_15_31529 : exactInterval 15 31529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31529 : oddCount 31529 15 = 10 ∧ acceleratedOrbit 15 31529 = 56821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31529) = 3 ^ 10 * m + 56821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31529.1, data_15_31529.2]

/-- Complete interval computation for depth 15, residue 31530. -/
theorem bounds_15_31530 : exactInterval 15 31530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31530 : oddCount 31530 15 = 3 ∧ acceleratedOrbit 15 31530 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31530) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31530.1, data_15_31530.2]

/-- Complete interval computation for depth 15, residue 31531. -/
theorem bounds_15_31531 : exactInterval 15 31531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31531 : oddCount 31531 15 = 9 ∧ acceleratedOrbit 15 31531 = 18944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31531) = 3 ^ 9 * m + 18944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31531.1, data_15_31531.2]

/-- Complete interval computation for depth 15, residue 31532. -/
theorem bounds_15_31532 : exactInterval 15 31532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31532 : oddCount 31532 15 = 9 ∧ acceleratedOrbit 15 31532 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31532) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31532.1, data_15_31532.2]

/-- Complete interval computation for depth 15, residue 31533. -/
theorem bounds_15_31533 : exactInterval 15 31533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31533 : oddCount 31533 15 = 9 ∧ acceleratedOrbit 15 31533 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31533) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31533.1, data_15_31533.2]

/-- Complete interval computation for depth 15, residue 31534. -/
theorem bounds_15_31534 : exactInterval 15 31534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31534 : oddCount 31534 15 = 9 ∧ acceleratedOrbit 15 31534 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31534) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31534.1, data_15_31534.2]

/-- Complete interval computation for depth 15, residue 31535. -/
theorem bounds_15_31535 : exactInterval 15 31535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31535 : oddCount 31535 15 = 9 ∧ acceleratedOrbit 15 31535 = 18944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31535) = 3 ^ 9 * m + 18944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31535.1, data_15_31535.2]

/-- Complete interval computation for depth 15, residue 31536. -/
theorem bounds_15_31536 : exactInterval 15 31536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31536 : oddCount 31536 15 = 3 ∧ acceleratedOrbit 15 31536 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31536) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31536.1, data_15_31536.2]

/-- Complete interval computation for depth 15, residue 31537. -/
theorem bounds_15_31537 : exactInterval 15 31537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31537 : oddCount 31537 15 = 9 ∧ acceleratedOrbit 15 31537 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31537) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31537.1, data_15_31537.2]

/-- Complete interval computation for depth 15, residue 31538. -/
theorem bounds_15_31538 : exactInterval 15 31538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31538 : oddCount 31538 15 = 9 ∧ acceleratedOrbit 15 31538 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31538) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31538.1, data_15_31538.2]

/-- Complete interval computation for depth 15, residue 31539. -/
theorem bounds_15_31539 : exactInterval 15 31539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31539 : oddCount 31539 15 = 9 ∧ acceleratedOrbit 15 31539 = 18953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31539) = 3 ^ 9 * m + 18953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31539.1, data_15_31539.2]

/-- Complete interval computation for depth 15, residue 31540. -/
theorem bounds_15_31540 : exactInterval 15 31540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31540 : oddCount 31540 15 = 3 ∧ acceleratedOrbit 15 31540 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31540) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31540.1, data_15_31540.2]

/-- Complete interval computation for depth 15, residue 31541. -/
theorem bounds_15_31541 : exactInterval 15 31541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31541 : oddCount 31541 15 = 3 ∧ acceleratedOrbit 15 31541 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31541) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31541.1, data_15_31541.2]

/-- Complete interval computation for depth 15, residue 31542. -/
theorem bounds_15_31542 : exactInterval 15 31542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31542 : oddCount 31542 15 = 9 ∧ acceleratedOrbit 15 31542 = 18949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31542) = 3 ^ 9 * m + 18949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31542.1, data_15_31542.2]

/-- Complete interval computation for depth 15, residue 31543. -/
theorem bounds_15_31543 : exactInterval 15 31543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31543 : oddCount 31543 15 = 9 ∧ acceleratedOrbit 15 31543 = 18949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31543) = 3 ^ 9 * m + 18949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31543.1, data_15_31543.2]

/-- Complete interval computation for depth 15, residue 31544. -/
theorem bounds_15_31544 : exactInterval 15 31544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31544 : oddCount 31544 15 = 11 ∧ acceleratedOrbit 15 31544 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31544) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31544.1, data_15_31544.2]

/-- Complete interval computation for depth 15, residue 31545. -/
theorem bounds_15_31545 : exactInterval 15 31545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31545 : oddCount 31545 15 = 10 ∧ acceleratedOrbit 15 31545 = 56852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31545) = 3 ^ 10 * m + 56852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31545.1, data_15_31545.2]

/-- Complete interval computation for depth 15, residue 31546. -/
theorem bounds_15_31546 : exactInterval 15 31546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31546 : oddCount 31546 15 = 11 ∧ acceleratedOrbit 15 31546 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31546) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31546.1, data_15_31546.2]

/-- Complete interval computation for depth 15, residue 31547. -/
theorem bounds_15_31547 : exactInterval 15 31547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31547 : oddCount 31547 15 = 10 ∧ acceleratedOrbit 15 31547 = 56861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31547) = 3 ^ 10 * m + 56861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31547.1, data_15_31547.2]

/-- Complete interval computation for depth 15, residue 31548. -/
theorem bounds_15_31548 : exactInterval 15 31548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31548 : oddCount 31548 15 = 11 ∧ acceleratedOrbit 15 31548 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31548) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31548.1, data_15_31548.2]

/-- Complete interval computation for depth 15, residue 31549. -/
theorem bounds_15_31549 : exactInterval 15 31549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31549 : oddCount 31549 15 = 11 ∧ acceleratedOrbit 15 31549 = 170585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31549) = 3 ^ 11 * m + 170585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31549.1, data_15_31549.2]

/-- Complete interval computation for depth 15, residue 31550. -/
theorem bounds_15_31550 : exactInterval 15 31550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31550 : oddCount 31550 15 = 11 ∧ acceleratedOrbit 15 31550 = 170576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31550) = 3 ^ 11 * m + 170576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31550.1, data_15_31550.2]

/-- Complete interval computation for depth 15, residue 31551. -/
theorem bounds_15_31551 : exactInterval 15 31551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31551 : oddCount 31551 15 = 11 ∧ acceleratedOrbit 15 31551 = 170576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31551) = 3 ^ 11 * m + 170576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31551.1, data_15_31551.2]

/-- Complete interval computation for depth 15, residue 31552. -/
theorem bounds_15_31552 : exactInterval 15 31552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31552 : oddCount 31552 15 = 5 ∧ acceleratedOrbit 15 31552 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31552) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31552.1, data_15_31552.2]

/-- Complete interval computation for depth 15, residue 31553. -/
theorem bounds_15_31553 : exactInterval 15 31553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31553 : oddCount 31553 15 = 3 ∧ acceleratedOrbit 15 31553 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31553) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31553.1, data_15_31553.2]

/-- Complete interval computation for depth 15, residue 31554. -/
theorem bounds_15_31554 : exactInterval 15 31554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31554 : oddCount 31554 15 = 8 ∧ acceleratedOrbit 15 31554 = 6320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31554) = 3 ^ 8 * m + 6320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31554.1, data_15_31554.2]

end Collatz.Research.PassageAtlas.Batch0963
