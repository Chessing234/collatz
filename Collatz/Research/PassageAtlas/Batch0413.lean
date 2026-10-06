import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0413

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13500. -/
theorem bounds_15_13500 : exactInterval 15 13500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13500 : oddCount 13500 15 = 9 ∧ acceleratedOrbit 15 13500 = 8113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13500) = 3 ^ 9 * m + 8113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13500.1, data_15_13500.2]

/-- Complete interval computation for depth 15, residue 13501. -/
theorem bounds_15_13501 : exactInterval 15 13501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13501 : oddCount 13501 15 = 9 ∧ acceleratedOrbit 15 13501 = 8113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13501) = 3 ^ 9 * m + 8113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13501.1, data_15_13501.2]

/-- Complete interval computation for depth 15, residue 13502. -/
theorem bounds_15_13502 : exactInterval 15 13502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13502 : oddCount 13502 15 = 9 ∧ acceleratedOrbit 15 13502 = 8113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13502) = 3 ^ 9 * m + 8113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13502.1, data_15_13502.2]

/-- Complete interval computation for depth 15, residue 13503. -/
theorem bounds_15_13503 : exactInterval 15 13503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13503 : oddCount 13503 15 = 11 ∧ acceleratedOrbit 15 13503 = 73007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13503) = 3 ^ 11 * m + 73007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13503.1, data_15_13503.2]

/-- Complete interval computation for depth 15, residue 13504. -/
theorem bounds_15_13504 : exactInterval 15 13504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13504 : oddCount 13504 15 = 5 ∧ acceleratedOrbit 15 13504 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13504) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13504.1, data_15_13504.2]

/-- Complete interval computation for depth 15, residue 13505. -/
theorem bounds_15_13505 : exactInterval 15 13505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13505 : oddCount 13505 15 = 7 ∧ acceleratedOrbit 15 13505 = 902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13505) = 3 ^ 7 * m + 902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13505.1, data_15_13505.2]

/-- Complete interval computation for depth 15, residue 13506. -/
theorem bounds_15_13506 : exactInterval 15 13506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13506 : oddCount 13506 15 = 7 ∧ acceleratedOrbit 15 13506 = 902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13506) = 3 ^ 7 * m + 902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13506.1, data_15_13506.2]

/-- Complete interval computation for depth 15, residue 13507. -/
theorem bounds_15_13507 : exactInterval 15 13507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13507 : oddCount 13507 15 = 7 ∧ acceleratedOrbit 15 13507 = 902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13507) = 3 ^ 7 * m + 902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13507.1, data_15_13507.2]

/-- Complete interval computation for depth 15, residue 13508. -/
theorem bounds_15_13508 : exactInterval 15 13508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13508 : oddCount 13508 15 = 7 ∧ acceleratedOrbit 15 13508 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13508) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13508.1, data_15_13508.2]

/-- Complete interval computation for depth 15, residue 13509. -/
theorem bounds_15_13509 : exactInterval 15 13509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13509 : oddCount 13509 15 = 7 ∧ acceleratedOrbit 15 13509 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13509) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13509.1, data_15_13509.2]

/-- Complete interval computation for depth 15, residue 13510. -/
theorem bounds_15_13510 : exactInterval 15 13510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13510 : oddCount 13510 15 = 7 ∧ acceleratedOrbit 15 13510 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13510) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13510.1, data_15_13510.2]

/-- Complete interval computation for depth 15, residue 13511. -/
theorem bounds_15_13511 : exactInterval 15 13511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13511 : oddCount 13511 15 = 7 ∧ acceleratedOrbit 15 13511 = 902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13511) = 3 ^ 7 * m + 902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13511.1, data_15_13511.2]

/-- Complete interval computation for depth 15, residue 13512. -/
theorem bounds_15_13512 : exactInterval 15 13512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13512 : oddCount 13512 15 = 7 ∧ acceleratedOrbit 15 13512 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13512) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13512.1, data_15_13512.2]

/-- Complete interval computation for depth 15, residue 13513. -/
theorem bounds_15_13513 : exactInterval 15 13513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13513 : oddCount 13513 15 = 6 ∧ acceleratedOrbit 15 13513 = 301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13513) = 3 ^ 6 * m + 301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13513.1, data_15_13513.2]

/-- Complete interval computation for depth 15, residue 13514. -/
theorem bounds_15_13514 : exactInterval 15 13514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13514 : oddCount 13514 15 = 7 ∧ acceleratedOrbit 15 13514 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13514) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13514.1, data_15_13514.2]

/-- Complete interval computation for depth 15, residue 13515. -/
theorem bounds_15_13515 : exactInterval 15 13515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13515 : oddCount 13515 15 = 6 ∧ acceleratedOrbit 15 13515 = 301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13515) = 3 ^ 6 * m + 301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13515.1, data_15_13515.2]

/-- Complete interval computation for depth 15, residue 13516. -/
theorem bounds_15_13516 : exactInterval 15 13516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13516 : oddCount 13516 15 = 7 ∧ acceleratedOrbit 15 13516 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13516) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13516.1, data_15_13516.2]

/-- Complete interval computation for depth 15, residue 13517. -/
theorem bounds_15_13517 : exactInterval 15 13517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13517 : oddCount 13517 15 = 7 ∧ acceleratedOrbit 15 13517 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13517) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13517.1, data_15_13517.2]

/-- Complete interval computation for depth 15, residue 13518. -/
theorem bounds_15_13518 : exactInterval 15 13518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13518 : oddCount 13518 15 = 9 ∧ acceleratedOrbit 15 13518 = 8122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13518) = 3 ^ 9 * m + 8122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13518.1, data_15_13518.2]

/-- Complete interval computation for depth 15, residue 13519. -/
theorem bounds_15_13519 : exactInterval 15 13519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13519 : oddCount 13519 15 = 9 ∧ acceleratedOrbit 15 13519 = 8122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13519) = 3 ^ 9 * m + 8122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13519.1, data_15_13519.2]

/-- Complete interval computation for depth 15, residue 13520. -/
theorem bounds_15_13520 : exactInterval 15 13520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13520 : oddCount 13520 15 = 5 ∧ acceleratedOrbit 15 13520 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13520) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13520.1, data_15_13520.2]

/-- Complete interval computation for depth 15, residue 13521. -/
theorem bounds_15_13521 : exactInterval 15 13521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13521 : oddCount 13521 15 = 9 ∧ acceleratedOrbit 15 13521 = 8126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13521) = 3 ^ 9 * m + 8126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13521.1, data_15_13521.2]

/-- Complete interval computation for depth 15, residue 13522. -/
theorem bounds_15_13522 : exactInterval 15 13522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13522 : oddCount 13522 15 = 9 ∧ acceleratedOrbit 15 13522 = 8126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13522) = 3 ^ 9 * m + 8126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13522.1, data_15_13522.2]

/-- Complete interval computation for depth 15, residue 13523. -/
theorem bounds_15_13523 : exactInterval 15 13523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13523 : oddCount 13523 15 = 9 ∧ acceleratedOrbit 15 13523 = 8126 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13523) = 3 ^ 9 * m + 8126 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13523.1, data_15_13523.2]

/-- Complete interval computation for depth 15, residue 13524. -/
theorem bounds_15_13524 : exactInterval 15 13524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13524 : oddCount 13524 15 = 5 ∧ acceleratedOrbit 15 13524 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13524) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13524.1, data_15_13524.2]

/-- Complete interval computation for depth 15, residue 13525. -/
theorem bounds_15_13525 : exactInterval 15 13525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13525 : oddCount 13525 15 = 5 ∧ acceleratedOrbit 15 13525 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13525) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13525.1, data_15_13525.2]

/-- Complete interval computation for depth 15, residue 13526. -/
theorem bounds_15_13526 : exactInterval 15 13526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13526 : oddCount 13526 15 = 6 ∧ acceleratedOrbit 15 13526 = 301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13526) = 3 ^ 6 * m + 301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13526.1, data_15_13526.2]

/-- Complete interval computation for depth 15, residue 13527. -/
theorem bounds_15_13527 : exactInterval 15 13527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13527 : oddCount 13527 15 = 6 ∧ acceleratedOrbit 15 13527 = 301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13527) = 3 ^ 6 * m + 301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13527.1, data_15_13527.2]

/-- Complete interval computation for depth 15, residue 13528. -/
theorem bounds_15_13528 : exactInterval 15 13528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13528 : oddCount 13528 15 = 8 ∧ acceleratedOrbit 15 13528 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13528) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13528.1, data_15_13528.2]

/-- Complete interval computation for depth 15, residue 13529. -/
theorem bounds_15_13529 : exactInterval 15 13529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13529 : oddCount 13529 15 = 7 ∧ acceleratedOrbit 15 13529 = 904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13529) = 3 ^ 7 * m + 904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13529.1, data_15_13529.2]

/-- Complete interval computation for depth 15, residue 13530. -/
theorem bounds_15_13530 : exactInterval 15 13530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13530 : oddCount 13530 15 = 8 ∧ acceleratedOrbit 15 13530 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13530) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13530.1, data_15_13530.2]

/-- Complete interval computation for depth 15, residue 13531. -/
theorem bounds_15_13531 : exactInterval 15 13531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13531 : oddCount 13531 15 = 8 ∧ acceleratedOrbit 15 13531 = 2710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13531) = 3 ^ 8 * m + 2710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13531.1, data_15_13531.2]

/-- Complete interval computation for depth 15, residue 13532. -/
theorem bounds_15_13532 : exactInterval 15 13532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13532 : oddCount 13532 15 = 8 ∧ acceleratedOrbit 15 13532 = 2711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13532) = 3 ^ 8 * m + 2711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13532.1, data_15_13532.2]

end Collatz.Research.PassageAtlas.Batch0413
