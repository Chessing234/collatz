import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0750

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24543. -/
theorem bounds_15_24543 : exactInterval 15 24543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24543 : oddCount 24543 15 = 9 ∧ acceleratedOrbit 15 24543 = 14744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24543) = 3 ^ 9 * m + 14744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24543.1, data_15_24543.2]

/-- Complete interval computation for depth 15, residue 24544. -/
theorem bounds_15_24544 : exactInterval 15 24544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24544 : oddCount 24544 15 = 9 ∧ acceleratedOrbit 15 24544 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24544) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24544.1, data_15_24544.2]

/-- Complete interval computation for depth 15, residue 24545. -/
theorem bounds_15_24545 : exactInterval 15 24545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24545 : oddCount 24545 15 = 10 ∧ acceleratedOrbit 15 24545 = 44236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24545) = 3 ^ 10 * m + 44236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24545.1, data_15_24545.2]

/-- Complete interval computation for depth 15, residue 24546. -/
theorem bounds_15_24546 : exactInterval 15 24546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24546 : oddCount 24546 15 = 7 ∧ acceleratedOrbit 15 24546 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24546) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24546.1, data_15_24546.2]

/-- Complete interval computation for depth 15, residue 24547. -/
theorem bounds_15_24547 : exactInterval 15 24547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24547 : oddCount 24547 15 = 7 ∧ acceleratedOrbit 15 24547 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24547) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24547.1, data_15_24547.2]

/-- Complete interval computation for depth 15, residue 24548. -/
theorem bounds_15_24548 : exactInterval 15 24548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24548 : oddCount 24548 15 = 7 ∧ acceleratedOrbit 15 24548 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24548) = 3 ^ 7 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24548.1, data_15_24548.2]

/-- Complete interval computation for depth 15, residue 24549. -/
theorem bounds_15_24549 : exactInterval 15 24549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24549 : oddCount 24549 15 = 7 ∧ acceleratedOrbit 15 24549 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24549) = 3 ^ 7 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24549.1, data_15_24549.2]

/-- Complete interval computation for depth 15, residue 24550. -/
theorem bounds_15_24550 : exactInterval 15 24550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24550 : oddCount 24550 15 = 7 ∧ acceleratedOrbit 15 24550 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24550) = 3 ^ 7 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24550.1, data_15_24550.2]

/-- Complete interval computation for depth 15, residue 24551. -/
theorem bounds_15_24551 : exactInterval 15 24551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24551 : oddCount 24551 15 = 10 ∧ acceleratedOrbit 15 24551 = 44246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24551) = 3 ^ 10 * m + 44246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24551.1, data_15_24551.2]

/-- Complete interval computation for depth 15, residue 24552. -/
theorem bounds_15_24552 : exactInterval 15 24552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24552 : oddCount 24552 15 = 9 ∧ acceleratedOrbit 15 24552 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24552) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24552.1, data_15_24552.2]

/-- Complete interval computation for depth 15, residue 24553. -/
theorem bounds_15_24553 : exactInterval 15 24553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24553 : oddCount 24553 15 = 9 ∧ acceleratedOrbit 15 24553 = 14750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24553) = 3 ^ 9 * m + 14750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24553.1, data_15_24553.2]

/-- Complete interval computation for depth 15, residue 24554. -/
theorem bounds_15_24554 : exactInterval 15 24554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24554 : oddCount 24554 15 = 9 ∧ acceleratedOrbit 15 24554 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24554) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24554.1, data_15_24554.2]

/-- Complete interval computation for depth 15, residue 24555. -/
theorem bounds_15_24555 : exactInterval 15 24555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24555 : oddCount 24555 15 = 12 ∧ acceleratedOrbit 15 24555 = 398276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24555) = 3 ^ 12 * m + 398276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24555.1, data_15_24555.2]

/-- Complete interval computation for depth 15, residue 24556. -/
theorem bounds_15_24556 : exactInterval 15 24556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24556 : oddCount 24556 15 = 9 ∧ acceleratedOrbit 15 24556 = 14755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24556) = 3 ^ 9 * m + 14755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24556.1, data_15_24556.2]

/-- Complete interval computation for depth 15, residue 24557. -/
theorem bounds_15_24557 : exactInterval 15 24557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24557 : oddCount 24557 15 = 9 ∧ acceleratedOrbit 15 24557 = 14755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24557) = 3 ^ 9 * m + 14755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24557.1, data_15_24557.2]

/-- Complete interval computation for depth 15, residue 24558. -/
theorem bounds_15_24558 : exactInterval 15 24558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24558 : oddCount 24558 15 = 9 ∧ acceleratedOrbit 15 24558 = 14755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24558) = 3 ^ 9 * m + 14755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24558.1, data_15_24558.2]

/-- Complete interval computation for depth 15, residue 24559. -/
theorem bounds_15_24559 : exactInterval 15 24559 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24559) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24559 : oddCount 24559 15 = 9 ∧ acceleratedOrbit 15 24559 = 14753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24559) = 3 ^ 9 * m + 14753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24559.1, data_15_24559.2]

/-- Complete interval computation for depth 15, residue 24560. -/
theorem bounds_15_24560 : exactInterval 15 24560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24560 : oddCount 24560 15 = 9 ∧ acceleratedOrbit 15 24560 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24560) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24560.1, data_15_24560.2]

/-- Complete interval computation for depth 15, residue 24561. -/
theorem bounds_15_24561 : exactInterval 15 24561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24561 : oddCount 24561 15 = 9 ∧ acceleratedOrbit 15 24561 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24561) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24561.1, data_15_24561.2]

/-- Complete interval computation for depth 15, residue 24562. -/
theorem bounds_15_24562 : exactInterval 15 24562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24562 : oddCount 24562 15 = 8 ∧ acceleratedOrbit 15 24562 = 4919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24562) = 3 ^ 8 * m + 4919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24562.1, data_15_24562.2]

/-- Complete interval computation for depth 15, residue 24563. -/
theorem bounds_15_24563 : exactInterval 15 24563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24563 : oddCount 24563 15 = 8 ∧ acceleratedOrbit 15 24563 = 4919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24563) = 3 ^ 8 * m + 4919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24563.1, data_15_24563.2]

/-- Complete interval computation for depth 15, residue 24564. -/
theorem bounds_15_24564 : exactInterval 15 24564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24564 : oddCount 24564 15 = 9 ∧ acceleratedOrbit 15 24564 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24564) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24564.1, data_15_24564.2]

/-- Complete interval computation for depth 15, residue 24565. -/
theorem bounds_15_24565 : exactInterval 15 24565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24565 : oddCount 24565 15 = 9 ∧ acceleratedOrbit 15 24565 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24565) = 3 ^ 9 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24565.1, data_15_24565.2]

/-- Complete interval computation for depth 15, residue 24566. -/
theorem bounds_15_24566 : exactInterval 15 24566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24566 : oddCount 24566 15 = 9 ∧ acceleratedOrbit 15 24566 = 14759 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24566) = 3 ^ 9 * m + 14759 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24566.1, data_15_24566.2]

/-- Complete interval computation for depth 15, residue 24567. -/
theorem bounds_15_24567 : exactInterval 15 24567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24567 : oddCount 24567 15 = 9 ∧ acceleratedOrbit 15 24567 = 14759 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24567) = 3 ^ 9 * m + 14759 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24567.1, data_15_24567.2]

/-- Complete interval computation for depth 15, residue 24568. -/
theorem bounds_15_24568 : exactInterval 15 24568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24568 : oddCount 24568 15 = 11 ∧ acceleratedOrbit 15 24568 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24568) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24568.1, data_15_24568.2]

/-- Complete interval computation for depth 15, residue 24569. -/
theorem bounds_15_24569 : exactInterval 15 24569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24569 : oddCount 24569 15 = 11 ∧ acceleratedOrbit 15 24569 = 132839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24569) = 3 ^ 11 * m + 132839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24569.1, data_15_24569.2]

/-- Complete interval computation for depth 15, residue 24570. -/
theorem bounds_15_24570 : exactInterval 15 24570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24570 : oddCount 24570 15 = 11 ∧ acceleratedOrbit 15 24570 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24570) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24570.1, data_15_24570.2]

/-- Complete interval computation for depth 15, residue 24571. -/
theorem bounds_15_24571 : exactInterval 15 24571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24571 : oddCount 24571 15 = 10 ∧ acceleratedOrbit 15 24571 = 44282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24571) = 3 ^ 10 * m + 44282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24571.1, data_15_24571.2]

/-- Complete interval computation for depth 15, residue 24572. -/
theorem bounds_15_24572 : exactInterval 15 24572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24572 : oddCount 24572 15 = 11 ∧ acceleratedOrbit 15 24572 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24572) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24572.1, data_15_24572.2]

/-- Complete interval computation for depth 15, residue 24573. -/
theorem bounds_15_24573 : exactInterval 15 24573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24573 : oddCount 24573 15 = 11 ∧ acceleratedOrbit 15 24573 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24573) = 3 ^ 11 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24573.1, data_15_24573.2]

/-- Complete interval computation for depth 15, residue 24574. -/
theorem bounds_15_24574 : exactInterval 15 24574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24574 : oddCount 24574 15 = 13 ∧ acceleratedOrbit 15 24574 = 1195742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24574) = 3 ^ 13 * m + 1195742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24574.1, data_15_24574.2]

/-- Complete interval computation for depth 15, residue 24575. -/
theorem bounds_15_24575 : exactInterval 15 24575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24575 : oddCount 24575 15 = 13 ∧ acceleratedOrbit 15 24575 = 1195742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24575) = 3 ^ 13 * m + 1195742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24575.1, data_15_24575.2]

end Collatz.Research.PassageAtlas.Batch0750
