import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0657

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21495. -/
theorem bounds_15_21495 : exactInterval 15 21495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21495 : oddCount 21495 15 = 7 ∧ acceleratedOrbit 15 21495 = 1435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21495) = 3 ^ 7 * m + 1435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21495.1, data_15_21495.2]

/-- Complete interval computation for depth 15, residue 21496. -/
theorem bounds_15_21496 : exactInterval 15 21496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21496 : oddCount 21496 15 = 9 ∧ acceleratedOrbit 15 21496 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21496) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21496.1, data_15_21496.2]

/-- Complete interval computation for depth 15, residue 21497. -/
theorem bounds_15_21497 : exactInterval 15 21497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21497 : oddCount 21497 15 = 10 ∧ acceleratedOrbit 15 21497 = 38744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21497) = 3 ^ 10 * m + 38744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21497.1, data_15_21497.2]

/-- Complete interval computation for depth 15, residue 21498. -/
theorem bounds_15_21498 : exactInterval 15 21498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21498 : oddCount 21498 15 = 9 ∧ acceleratedOrbit 15 21498 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21498) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21498.1, data_15_21498.2]

/-- Complete interval computation for depth 15, residue 21499. -/
theorem bounds_15_21499 : exactInterval 15 21499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21499 : oddCount 21499 15 = 7 ∧ acceleratedOrbit 15 21499 = 1435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21499) = 3 ^ 7 * m + 1435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21499.1, data_15_21499.2]

/-- Complete interval computation for depth 15, residue 21500. -/
theorem bounds_15_21500 : exactInterval 15 21500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21500 : oddCount 21500 15 = 9 ∧ acceleratedOrbit 15 21500 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21500) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21500.1, data_15_21500.2]

/-- Complete interval computation for depth 15, residue 21501. -/
theorem bounds_15_21501 : exactInterval 15 21501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21501 : oddCount 21501 15 = 9 ∧ acceleratedOrbit 15 21501 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21501) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21501.1, data_15_21501.2]

/-- Complete interval computation for depth 15, residue 21502. -/
theorem bounds_15_21502 : exactInterval 15 21502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21502 : oddCount 21502 15 = 13 ∧ acceleratedOrbit 15 21502 = 1046276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21502) = 3 ^ 13 * m + 1046276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21502.1, data_15_21502.2]

/-- Complete interval computation for depth 15, residue 21503. -/
theorem bounds_15_21503 : exactInterval 15 21503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21503 : oddCount 21503 15 = 13 ∧ acceleratedOrbit 15 21503 = 1046276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21503) = 3 ^ 13 * m + 1046276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21503.1, data_15_21503.2]

/-- Complete interval computation for depth 15, residue 21504. -/
theorem bounds_15_21504 : exactInterval 15 21504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21504 : oddCount 21504 15 = 1 ∧ acceleratedOrbit 15 21504 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21504) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21504.1, data_15_21504.2]

/-- Complete interval computation for depth 15, residue 21505. -/
theorem bounds_15_21505 : exactInterval 15 21505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21505 : oddCount 21505 15 = 6 ∧ acceleratedOrbit 15 21505 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21505) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21505.1, data_15_21505.2]

/-- Complete interval computation for depth 15, residue 21506. -/
theorem bounds_15_21506 : exactInterval 15 21506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21506 : oddCount 21506 15 = 7 ∧ acceleratedOrbit 15 21506 = 1436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21506) = 3 ^ 7 * m + 1436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21506.1, data_15_21506.2]

/-- Complete interval computation for depth 15, residue 21507. -/
theorem bounds_15_21507 : exactInterval 15 21507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21507 : oddCount 21507 15 = 7 ∧ acceleratedOrbit 15 21507 = 1436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21507) = 3 ^ 7 * m + 1436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21507.1, data_15_21507.2]

/-- Complete interval computation for depth 15, residue 21508. -/
theorem bounds_15_21508 : exactInterval 15 21508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21508 : oddCount 21508 15 = 6 ∧ acceleratedOrbit 15 21508 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21508) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21508.1, data_15_21508.2]

/-- Complete interval computation for depth 15, residue 21509. -/
theorem bounds_15_21509 : exactInterval 15 21509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21509 : oddCount 21509 15 = 6 ∧ acceleratedOrbit 15 21509 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21509) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21509.1, data_15_21509.2]

/-- Complete interval computation for depth 15, residue 21510. -/
theorem bounds_15_21510 : exactInterval 15 21510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21510 : oddCount 21510 15 = 6 ∧ acceleratedOrbit 15 21510 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21510) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21510.1, data_15_21510.2]

/-- Complete interval computation for depth 15, residue 21511. -/
theorem bounds_15_21511 : exactInterval 15 21511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21511 : oddCount 21511 15 = 7 ∧ acceleratedOrbit 15 21511 = 1436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21511) = 3 ^ 7 * m + 1436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21511.1, data_15_21511.2]

/-- Complete interval computation for depth 15, residue 21512. -/
theorem bounds_15_21512 : exactInterval 15 21512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21512 : oddCount 21512 15 = 8 ∧ acceleratedOrbit 15 21512 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21512) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21512.1, data_15_21512.2]

/-- Complete interval computation for depth 15, residue 21513. -/
theorem bounds_15_21513 : exactInterval 15 21513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21513 : oddCount 21513 15 = 7 ∧ acceleratedOrbit 15 21513 = 1436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21513) = 3 ^ 7 * m + 1436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21513.1, data_15_21513.2]

/-- Complete interval computation for depth 15, residue 21514. -/
theorem bounds_15_21514 : exactInterval 15 21514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21514 : oddCount 21514 15 = 8 ∧ acceleratedOrbit 15 21514 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21514) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21514.1, data_15_21514.2]

/-- Complete interval computation for depth 15, residue 21515. -/
theorem bounds_15_21515 : exactInterval 15 21515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21515 : oddCount 21515 15 = 6 ∧ acceleratedOrbit 15 21515 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21515) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21515.1, data_15_21515.2]

/-- Complete interval computation for depth 15, residue 21516. -/
theorem bounds_15_21516 : exactInterval 15 21516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21516 : oddCount 21516 15 = 8 ∧ acceleratedOrbit 15 21516 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21516) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21516.1, data_15_21516.2]

/-- Complete interval computation for depth 15, residue 21517. -/
theorem bounds_15_21517 : exactInterval 15 21517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21517 : oddCount 21517 15 = 8 ∧ acceleratedOrbit 15 21517 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21517) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21517.1, data_15_21517.2]

/-- Complete interval computation for depth 15, residue 21518. -/
theorem bounds_15_21518 : exactInterval 15 21518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21518 : oddCount 21518 15 = 8 ∧ acceleratedOrbit 15 21518 = 4310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21518) = 3 ^ 8 * m + 4310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21518.1, data_15_21518.2]

/-- Complete interval computation for depth 15, residue 21519. -/
theorem bounds_15_21519 : exactInterval 15 21519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21519 : oddCount 21519 15 = 8 ∧ acceleratedOrbit 15 21519 = 4310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21519) = 3 ^ 8 * m + 4310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21519.1, data_15_21519.2]

/-- Complete interval computation for depth 15, residue 21520. -/
theorem bounds_15_21520 : exactInterval 15 21520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21520 : oddCount 21520 15 = 5 ∧ acceleratedOrbit 15 21520 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21520) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21520.1, data_15_21520.2]

/-- Complete interval computation for depth 15, residue 21521. -/
theorem bounds_15_21521 : exactInterval 15 21521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21521 : oddCount 21521 15 = 8 ∧ acceleratedOrbit 15 21521 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21521) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21521.1, data_15_21521.2]

/-- Complete interval computation for depth 15, residue 21522. -/
theorem bounds_15_21522 : exactInterval 15 21522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21522 : oddCount 21522 15 = 6 ∧ acceleratedOrbit 15 21522 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21522) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21522.1, data_15_21522.2]

/-- Complete interval computation for depth 15, residue 21523. -/
theorem bounds_15_21523 : exactInterval 15 21523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21523 : oddCount 21523 15 = 6 ∧ acceleratedOrbit 15 21523 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21523) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21523.1, data_15_21523.2]

/-- Complete interval computation for depth 15, residue 21524. -/
theorem bounds_15_21524 : exactInterval 15 21524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21524 : oddCount 21524 15 = 5 ∧ acceleratedOrbit 15 21524 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21524) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21524.1, data_15_21524.2]

/-- Complete interval computation for depth 15, residue 21525. -/
theorem bounds_15_21525 : exactInterval 15 21525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21525 : oddCount 21525 15 = 5 ∧ acceleratedOrbit 15 21525 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21525) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21525.1, data_15_21525.2]

/-- Complete interval computation for depth 15, residue 21526. -/
theorem bounds_15_21526 : exactInterval 15 21526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21526 : oddCount 21526 15 = 8 ∧ acceleratedOrbit 15 21526 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21526) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21526.1, data_15_21526.2]

/-- Complete interval computation for depth 15, residue 21527. -/
theorem bounds_15_21527 : exactInterval 15 21527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21527 : oddCount 21527 15 = 8 ∧ acceleratedOrbit 15 21527 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21527) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21527.1, data_15_21527.2]

end Collatz.Research.PassageAtlas.Batch0657
