import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0719

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23527. -/
theorem bounds_15_23527 : exactInterval 15 23527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23527 : oddCount 23527 15 = 9 ∧ acceleratedOrbit 15 23527 = 14134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23527) = 3 ^ 9 * m + 14134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23527.1, data_15_23527.2]

/-- Complete interval computation for depth 15, residue 23528. -/
theorem bounds_15_23528 : exactInterval 15 23528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23528 : oddCount 23528 15 = 6 ∧ acceleratedOrbit 15 23528 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23528) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23528.1, data_15_23528.2]

/-- Complete interval computation for depth 15, residue 23529. -/
theorem bounds_15_23529 : exactInterval 15 23529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23529 : oddCount 23529 15 = 12 ∧ acceleratedOrbit 15 23529 = 381631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23529) = 3 ^ 12 * m + 381631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23529.1, data_15_23529.2]

/-- Complete interval computation for depth 15, residue 23530. -/
theorem bounds_15_23530 : exactInterval 15 23530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23530 : oddCount 23530 15 = 6 ∧ acceleratedOrbit 15 23530 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23530) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23530.1, data_15_23530.2]

/-- Complete interval computation for depth 15, residue 23531. -/
theorem bounds_15_23531 : exactInterval 15 23531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23531 : oddCount 23531 15 = 8 ∧ acceleratedOrbit 15 23531 = 4712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23531) = 3 ^ 8 * m + 4712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23531.1, data_15_23531.2]

/-- Complete interval computation for depth 15, residue 23532. -/
theorem bounds_15_23532 : exactInterval 15 23532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23532 : oddCount 23532 15 = 7 ∧ acceleratedOrbit 15 23532 = 1571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23532) = 3 ^ 7 * m + 1571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23532.1, data_15_23532.2]

/-- Complete interval computation for depth 15, residue 23533. -/
theorem bounds_15_23533 : exactInterval 15 23533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23533 : oddCount 23533 15 = 7 ∧ acceleratedOrbit 15 23533 = 1571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23533) = 3 ^ 7 * m + 1571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23533.1, data_15_23533.2]

/-- Complete interval computation for depth 15, residue 23534. -/
theorem bounds_15_23534 : exactInterval 15 23534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23534 : oddCount 23534 15 = 7 ∧ acceleratedOrbit 15 23534 = 1571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23534) = 3 ^ 7 * m + 1571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23534.1, data_15_23534.2]

/-- Complete interval computation for depth 15, residue 23535. -/
theorem bounds_15_23535 : exactInterval 15 23535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23535 : oddCount 23535 15 = 11 ∧ acceleratedOrbit 15 23535 = 127241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23535) = 3 ^ 11 * m + 127241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23535.1, data_15_23535.2]

/-- Complete interval computation for depth 15, residue 23536. -/
theorem bounds_15_23536 : exactInterval 15 23536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23536 : oddCount 23536 15 = 10 ∧ acceleratedOrbit 15 23536 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23536) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23536.1, data_15_23536.2]

/-- Complete interval computation for depth 15, residue 23537. -/
theorem bounds_15_23537 : exactInterval 15 23537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23537 : oddCount 23537 15 = 6 ∧ acceleratedOrbit 15 23537 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23537) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23537.1, data_15_23537.2]

/-- Complete interval computation for depth 15, residue 23538. -/
theorem bounds_15_23538 : exactInterval 15 23538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23538 : oddCount 23538 15 = 8 ∧ acceleratedOrbit 15 23538 = 4715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23538) = 3 ^ 8 * m + 4715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23538.1, data_15_23538.2]

/-- Complete interval computation for depth 15, residue 23539. -/
theorem bounds_15_23539 : exactInterval 15 23539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23539 : oddCount 23539 15 = 8 ∧ acceleratedOrbit 15 23539 = 4715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23539) = 3 ^ 8 * m + 4715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23539.1, data_15_23539.2]

/-- Complete interval computation for depth 15, residue 23540. -/
theorem bounds_15_23540 : exactInterval 15 23540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23540 : oddCount 23540 15 = 10 ∧ acceleratedOrbit 15 23540 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23540) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23540.1, data_15_23540.2]

/-- Complete interval computation for depth 15, residue 23541. -/
theorem bounds_15_23541 : exactInterval 15 23541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23541 : oddCount 23541 15 = 10 ∧ acceleratedOrbit 15 23541 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23541) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23541.1, data_15_23541.2]

/-- Complete interval computation for depth 15, residue 23542. -/
theorem bounds_15_23542 : exactInterval 15 23542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23542 : oddCount 23542 15 = 8 ∧ acceleratedOrbit 15 23542 = 4715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23542) = 3 ^ 8 * m + 4715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23542.1, data_15_23542.2]

/-- Complete interval computation for depth 15, residue 23543. -/
theorem bounds_15_23543 : exactInterval 15 23543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23543 : oddCount 23543 15 = 8 ∧ acceleratedOrbit 15 23543 = 4715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23543) = 3 ^ 8 * m + 4715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23543.1, data_15_23543.2]

/-- Complete interval computation for depth 15, residue 23544. -/
theorem bounds_15_23544 : exactInterval 15 23544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23544 : oddCount 23544 15 = 10 ∧ acceleratedOrbit 15 23544 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23544) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23544.1, data_15_23544.2]

/-- Complete interval computation for depth 15, residue 23545. -/
theorem bounds_15_23545 : exactInterval 15 23545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23545 : oddCount 23545 15 = 10 ∧ acceleratedOrbit 15 23545 = 42434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23545) = 3 ^ 10 * m + 42434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23545.1, data_15_23545.2]

/-- Complete interval computation for depth 15, residue 23546. -/
theorem bounds_15_23546 : exactInterval 15 23546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23546 : oddCount 23546 15 = 10 ∧ acceleratedOrbit 15 23546 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23546) = 3 ^ 10 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23546.1, data_15_23546.2]

/-- Complete interval computation for depth 15, residue 23547. -/
theorem bounds_15_23547 : exactInterval 15 23547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23547 : oddCount 23547 15 = 10 ∧ acceleratedOrbit 15 23547 = 42437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23547) = 3 ^ 10 * m + 42437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23547.1, data_15_23547.2]

/-- Complete interval computation for depth 15, residue 23548. -/
theorem bounds_15_23548 : exactInterval 15 23548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23548 : oddCount 23548 15 = 11 ∧ acceleratedOrbit 15 23548 = 127325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23548) = 3 ^ 11 * m + 127325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23548.1, data_15_23548.2]

/-- Complete interval computation for depth 15, residue 23549. -/
theorem bounds_15_23549 : exactInterval 15 23549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23549 : oddCount 23549 15 = 11 ∧ acceleratedOrbit 15 23549 = 127325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23549) = 3 ^ 11 * m + 127325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23549.1, data_15_23549.2]

/-- Complete interval computation for depth 15, residue 23550. -/
theorem bounds_15_23550 : exactInterval 15 23550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23550 : oddCount 23550 15 = 11 ∧ acceleratedOrbit 15 23550 = 127325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23550) = 3 ^ 11 * m + 127325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23550.1, data_15_23550.2]

/-- Complete interval computation for depth 15, residue 23551. -/
theorem bounds_15_23551 : exactInterval 15 23551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23551 : oddCount 23551 15 = 13 ∧ acceleratedOrbit 15 23551 = 1145920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23551) = 3 ^ 13 * m + 1145920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23551.1, data_15_23551.2]

/-- Complete interval computation for depth 15, residue 23552. -/
theorem bounds_15_23552 : exactInterval 15 23552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23552 : oddCount 23552 15 = 3 ∧ acceleratedOrbit 15 23552 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23552) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23552.1, data_15_23552.2]

/-- Complete interval computation for depth 15, residue 23553. -/
theorem bounds_15_23553 : exactInterval 15 23553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23553 : oddCount 23553 15 = 8 ∧ acceleratedOrbit 15 23553 = 4718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23553) = 3 ^ 8 * m + 4718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23553.1, data_15_23553.2]

/-- Complete interval computation for depth 15, residue 23554. -/
theorem bounds_15_23554 : exactInterval 15 23554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23554 : oddCount 23554 15 = 8 ∧ acceleratedOrbit 15 23554 = 4718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23554) = 3 ^ 8 * m + 4718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23554.1, data_15_23554.2]

/-- Complete interval computation for depth 15, residue 23555. -/
theorem bounds_15_23555 : exactInterval 15 23555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23555 : oddCount 23555 15 = 8 ∧ acceleratedOrbit 15 23555 = 4718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23555) = 3 ^ 8 * m + 4718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23555.1, data_15_23555.2]

/-- Complete interval computation for depth 15, residue 23556. -/
theorem bounds_15_23556 : exactInterval 15 23556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23556 : oddCount 23556 15 = 5 ∧ acceleratedOrbit 15 23556 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23556) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23556.1, data_15_23556.2]

/-- Complete interval computation for depth 15, residue 23557. -/
theorem bounds_15_23557 : exactInterval 15 23557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23557 : oddCount 23557 15 = 5 ∧ acceleratedOrbit 15 23557 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23557) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23557.1, data_15_23557.2]

/-- Complete interval computation for depth 15, residue 23558. -/
theorem bounds_15_23558 : exactInterval 15 23558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23558 : oddCount 23558 15 = 5 ∧ acceleratedOrbit 15 23558 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23558) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23558.1, data_15_23558.2]

/-- Complete interval computation for depth 15, residue 23559. -/
theorem bounds_15_23559 : exactInterval 15 23559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23559 : oddCount 23559 15 = 8 ∧ acceleratedOrbit 15 23559 = 4718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23559) = 3 ^ 8 * m + 4718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23559.1, data_15_23559.2]

end Collatz.Research.PassageAtlas.Batch0719
