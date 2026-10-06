import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0475

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15532. -/
theorem bounds_15_15532 : exactInterval 15 15532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15532 : oddCount 15532 15 = 6 ∧ acceleratedOrbit 15 15532 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15532) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15532.1, data_15_15532.2]

/-- Complete interval computation for depth 15, residue 15533. -/
theorem bounds_15_15533 : exactInterval 15 15533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15533 : oddCount 15533 15 = 6 ∧ acceleratedOrbit 15 15533 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15533) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15533.1, data_15_15533.2]

/-- Complete interval computation for depth 15, residue 15534. -/
theorem bounds_15_15534 : exactInterval 15 15534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15534 : oddCount 15534 15 = 6 ∧ acceleratedOrbit 15 15534 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15534) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15534.1, data_15_15534.2]

/-- Complete interval computation for depth 15, residue 15535. -/
theorem bounds_15_15535 : exactInterval 15 15535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15535 : oddCount 15535 15 = 11 ∧ acceleratedOrbit 15 15535 = 83996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15535) = 3 ^ 11 * m + 83996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15535.1, data_15_15535.2]

/-- Complete interval computation for depth 15, residue 15536. -/
theorem bounds_15_15536 : exactInterval 15 15536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15536 : oddCount 15536 15 = 5 ∧ acceleratedOrbit 15 15536 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15536) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15536.1, data_15_15536.2]

/-- Complete interval computation for depth 15, residue 15537. -/
theorem bounds_15_15537 : exactInterval 15 15537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15537 : oddCount 15537 15 = 9 ∧ acceleratedOrbit 15 15537 = 9341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15537) = 3 ^ 9 * m + 9341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15537.1, data_15_15537.2]

/-- Complete interval computation for depth 15, residue 15538. -/
theorem bounds_15_15538 : exactInterval 15 15538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15538 : oddCount 15538 15 = 9 ∧ acceleratedOrbit 15 15538 = 9341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15538) = 3 ^ 9 * m + 9341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15538.1, data_15_15538.2]

/-- Complete interval computation for depth 15, residue 15539. -/
theorem bounds_15_15539 : exactInterval 15 15539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15539 : oddCount 15539 15 = 9 ∧ acceleratedOrbit 15 15539 = 9341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15539) = 3 ^ 9 * m + 9341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15539.1, data_15_15539.2]

/-- Complete interval computation for depth 15, residue 15540. -/
theorem bounds_15_15540 : exactInterval 15 15540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15540 : oddCount 15540 15 = 5 ∧ acceleratedOrbit 15 15540 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15540) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15540.1, data_15_15540.2]

/-- Complete interval computation for depth 15, residue 15541. -/
theorem bounds_15_15541 : exactInterval 15 15541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15541 : oddCount 15541 15 = 5 ∧ acceleratedOrbit 15 15541 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15541) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15541.1, data_15_15541.2]

/-- Complete interval computation for depth 15, residue 15542. -/
theorem bounds_15_15542 : exactInterval 15 15542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15542 : oddCount 15542 15 = 8 ∧ acceleratedOrbit 15 15542 = 3113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15542) = 3 ^ 8 * m + 3113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15542.1, data_15_15542.2]

/-- Complete interval computation for depth 15, residue 15543. -/
theorem bounds_15_15543 : exactInterval 15 15543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15543 : oddCount 15543 15 = 8 ∧ acceleratedOrbit 15 15543 = 3113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15543) = 3 ^ 8 * m + 3113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15543.1, data_15_15543.2]

/-- Complete interval computation for depth 15, residue 15544. -/
theorem bounds_15_15544 : exactInterval 15 15544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15544 : oddCount 15544 15 = 5 ∧ acceleratedOrbit 15 15544 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15544) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15544.1, data_15_15544.2]

/-- Complete interval computation for depth 15, residue 15545. -/
theorem bounds_15_15545 : exactInterval 15 15545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15545 : oddCount 15545 15 = 9 ∧ acceleratedOrbit 15 15545 = 9341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15545) = 3 ^ 9 * m + 9341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15545.1, data_15_15545.2]

/-- Complete interval computation for depth 15, residue 15546. -/
theorem bounds_15_15546 : exactInterval 15 15546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15546 : oddCount 15546 15 = 5 ∧ acceleratedOrbit 15 15546 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15546) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15546.1, data_15_15546.2]

/-- Complete interval computation for depth 15, residue 15547. -/
theorem bounds_15_15547 : exactInterval 15 15547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15547 : oddCount 15547 15 = 10 ∧ acceleratedOrbit 15 15547 = 28021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15547) = 3 ^ 10 * m + 28021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15547.1, data_15_15547.2]

/-- Complete interval computation for depth 15, residue 15548. -/
theorem bounds_15_15548 : exactInterval 15 15548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15548 : oddCount 15548 15 = 6 ∧ acceleratedOrbit 15 15548 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15548) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15548.1, data_15_15548.2]

/-- Complete interval computation for depth 15, residue 15549. -/
theorem bounds_15_15549 : exactInterval 15 15549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15549 : oddCount 15549 15 = 6 ∧ acceleratedOrbit 15 15549 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15549) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15549.1, data_15_15549.2]

/-- Complete interval computation for depth 15, residue 15550. -/
theorem bounds_15_15550 : exactInterval 15 15550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15550 : oddCount 15550 15 = 6 ∧ acceleratedOrbit 15 15550 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15550) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15550.1, data_15_15550.2]

/-- Complete interval computation for depth 15, residue 15551. -/
theorem bounds_15_15551 : exactInterval 15 15551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15551 : oddCount 15551 15 = 12 ∧ acceleratedOrbit 15 15551 = 252233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15551) = 3 ^ 12 * m + 252233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15551.1, data_15_15551.2]

/-- Complete interval computation for depth 15, residue 15552. -/
theorem bounds_15_15552 : exactInterval 15 15552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15552 : oddCount 15552 15 = 6 ∧ acceleratedOrbit 15 15552 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15552) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15552.1, data_15_15552.2]

/-- Complete interval computation for depth 15, residue 15553. -/
theorem bounds_15_15553 : exactInterval 15 15553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15553 : oddCount 15553 15 = 7 ∧ acceleratedOrbit 15 15553 = 1039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15553) = 3 ^ 7 * m + 1039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15553.1, data_15_15553.2]

/-- Complete interval computation for depth 15, residue 15554. -/
theorem bounds_15_15554 : exactInterval 15 15554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15554 : oddCount 15554 15 = 7 ∧ acceleratedOrbit 15 15554 = 1039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15554) = 3 ^ 7 * m + 1039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15554.1, data_15_15554.2]

/-- Complete interval computation for depth 15, residue 15555. -/
theorem bounds_15_15555 : exactInterval 15 15555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15555 : oddCount 15555 15 = 7 ∧ acceleratedOrbit 15 15555 = 1039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15555) = 3 ^ 7 * m + 1039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15555.1, data_15_15555.2]

/-- Complete interval computation for depth 15, residue 15556. -/
theorem bounds_15_15556 : exactInterval 15 15556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15556 : oddCount 15556 15 = 5 ∧ acceleratedOrbit 15 15556 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15556) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15556.1, data_15_15556.2]

/-- Complete interval computation for depth 15, residue 15557. -/
theorem bounds_15_15557 : exactInterval 15 15557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15557 : oddCount 15557 15 = 5 ∧ acceleratedOrbit 15 15557 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15557) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15557.1, data_15_15557.2]

/-- Complete interval computation for depth 15, residue 15558. -/
theorem bounds_15_15558 : exactInterval 15 15558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15558 : oddCount 15558 15 = 5 ∧ acceleratedOrbit 15 15558 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15558) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15558.1, data_15_15558.2]

/-- Complete interval computation for depth 15, residue 15559. -/
theorem bounds_15_15559 : exactInterval 15 15559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15559 : oddCount 15559 15 = 8 ∧ acceleratedOrbit 15 15559 = 3116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15559) = 3 ^ 8 * m + 3116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15559.1, data_15_15559.2]

/-- Complete interval computation for depth 15, residue 15560. -/
theorem bounds_15_15560 : exactInterval 15 15560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15560 : oddCount 15560 15 = 5 ∧ acceleratedOrbit 15 15560 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15560) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15560.1, data_15_15560.2]

/-- Complete interval computation for depth 15, residue 15561. -/
theorem bounds_15_15561 : exactInterval 15 15561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15561 : oddCount 15561 15 = 8 ∧ acceleratedOrbit 15 15561 = 3118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15561) = 3 ^ 8 * m + 3118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15561.1, data_15_15561.2]

/-- Complete interval computation for depth 15, residue 15562. -/
theorem bounds_15_15562 : exactInterval 15 15562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15562 : oddCount 15562 15 = 5 ∧ acceleratedOrbit 15 15562 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15562) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15562.1, data_15_15562.2]

/-- Complete interval computation for depth 15, residue 15563. -/
theorem bounds_15_15563 : exactInterval 15 15563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15563 : oddCount 15563 15 = 8 ∧ acceleratedOrbit 15 15563 = 3118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15563) = 3 ^ 8 * m + 3118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15563.1, data_15_15563.2]

end Collatz.Research.PassageAtlas.Batch0475
