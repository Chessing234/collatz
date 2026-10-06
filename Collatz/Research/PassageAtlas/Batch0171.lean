import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0171

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5570. -/
theorem bounds_15_5570 : exactInterval 15 5570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5570 : oddCount 5570 15 = 9 ∧ acceleratedOrbit 15 5570 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5570) = 3 ^ 9 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5570.1, data_15_5570.2]

/-- Complete interval computation for depth 15, residue 5571. -/
theorem bounds_15_5571 : exactInterval 15 5571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5571 : oddCount 5571 15 = 9 ∧ acceleratedOrbit 15 5571 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5571) = 3 ^ 9 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5571.1, data_15_5571.2]

/-- Complete interval computation for depth 15, residue 5572. -/
theorem bounds_15_5572 : exactInterval 15 5572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5572 : oddCount 5572 15 = 4 ∧ acceleratedOrbit 15 5572 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5572) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5572.1, data_15_5572.2]

/-- Complete interval computation for depth 15, residue 5573. -/
theorem bounds_15_5573 : exactInterval 15 5573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5573 : oddCount 5573 15 = 4 ∧ acceleratedOrbit 15 5573 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5573) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5573.1, data_15_5573.2]

/-- Complete interval computation for depth 15, residue 5574. -/
theorem bounds_15_5574 : exactInterval 15 5574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5574 : oddCount 5574 15 = 4 ∧ acceleratedOrbit 15 5574 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5574) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5574.1, data_15_5574.2]

/-- Complete interval computation for depth 15, residue 5575. -/
theorem bounds_15_5575 : exactInterval 15 5575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5575 : oddCount 5575 15 = 8 ∧ acceleratedOrbit 15 5575 = 1117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5575) = 3 ^ 8 * m + 1117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5575.1, data_15_5575.2]

/-- Complete interval computation for depth 15, residue 5576. -/
theorem bounds_15_5576 : exactInterval 15 5576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5576 : oddCount 5576 15 = 6 ∧ acceleratedOrbit 15 5576 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5576) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5576.1, data_15_5576.2]

/-- Complete interval computation for depth 15, residue 5577. -/
theorem bounds_15_5577 : exactInterval 15 5577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5577 : oddCount 5577 15 = 7 ∧ acceleratedOrbit 15 5577 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5577) = 3 ^ 7 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5577.1, data_15_5577.2]

/-- Complete interval computation for depth 15, residue 5578. -/
theorem bounds_15_5578 : exactInterval 15 5578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5578 : oddCount 5578 15 = 6 ∧ acceleratedOrbit 15 5578 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5578) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5578.1, data_15_5578.2]

/-- Complete interval computation for depth 15, residue 5579. -/
theorem bounds_15_5579 : exactInterval 15 5579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5579 : oddCount 5579 15 = 7 ∧ acceleratedOrbit 15 5579 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5579) = 3 ^ 7 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5579.1, data_15_5579.2]

/-- Complete interval computation for depth 15, residue 5580. -/
theorem bounds_15_5580 : exactInterval 15 5580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5580 : oddCount 5580 15 = 6 ∧ acceleratedOrbit 15 5580 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5580) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5580.1, data_15_5580.2]

/-- Complete interval computation for depth 15, residue 5581. -/
theorem bounds_15_5581 : exactInterval 15 5581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5581 : oddCount 5581 15 = 6 ∧ acceleratedOrbit 15 5581 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5581) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5581.1, data_15_5581.2]

/-- Complete interval computation for depth 15, residue 5582. -/
theorem bounds_15_5582 : exactInterval 15 5582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5582 : oddCount 5582 15 = 10 ∧ acceleratedOrbit 15 5582 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5582) = 3 ^ 10 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5582.1, data_15_5582.2]

/-- Complete interval computation for depth 15, residue 5583. -/
theorem bounds_15_5583 : exactInterval 15 5583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5583 : oddCount 5583 15 = 10 ∧ acceleratedOrbit 15 5583 = 10064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5583) = 3 ^ 10 * m + 10064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5583.1, data_15_5583.2]

/-- Complete interval computation for depth 15, residue 5584. -/
theorem bounds_15_5584 : exactInterval 15 5584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5584 : oddCount 5584 15 = 4 ∧ acceleratedOrbit 15 5584 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5584) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5584.1, data_15_5584.2]

/-- Complete interval computation for depth 15, residue 5585. -/
theorem bounds_15_5585 : exactInterval 15 5585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5585 : oddCount 5585 15 = 6 ∧ acceleratedOrbit 15 5585 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5585) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5585.1, data_15_5585.2]

/-- Complete interval computation for depth 15, residue 5586. -/
theorem bounds_15_5586 : exactInterval 15 5586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5586 : oddCount 5586 15 = 9 ∧ acceleratedOrbit 15 5586 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5586) = 3 ^ 9 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5586.1, data_15_5586.2]

/-- Complete interval computation for depth 15, residue 5587. -/
theorem bounds_15_5587 : exactInterval 15 5587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5587 : oddCount 5587 15 = 9 ∧ acceleratedOrbit 15 5587 = 3358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5587) = 3 ^ 9 * m + 3358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5587.1, data_15_5587.2]

/-- Complete interval computation for depth 15, residue 5588. -/
theorem bounds_15_5588 : exactInterval 15 5588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5588 : oddCount 5588 15 = 4 ∧ acceleratedOrbit 15 5588 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5588) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5588.1, data_15_5588.2]

/-- Complete interval computation for depth 15, residue 5589. -/
theorem bounds_15_5589 : exactInterval 15 5589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5589 : oddCount 5589 15 = 4 ∧ acceleratedOrbit 15 5589 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5589) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5589.1, data_15_5589.2]

/-- Complete interval computation for depth 15, residue 5590. -/
theorem bounds_15_5590 : exactInterval 15 5590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5590 : oddCount 5590 15 = 9 ∧ acceleratedOrbit 15 5590 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5590) = 3 ^ 9 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5590.1, data_15_5590.2]

/-- Complete interval computation for depth 15, residue 5591. -/
theorem bounds_15_5591 : exactInterval 15 5591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5591 : oddCount 5591 15 = 9 ∧ acceleratedOrbit 15 5591 = 3361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5591) = 3 ^ 9 * m + 3361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5591.1, data_15_5591.2]

/-- Complete interval computation for depth 15, residue 5592. -/
theorem bounds_15_5592 : exactInterval 15 5592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5592 : oddCount 5592 15 = 8 ∧ acceleratedOrbit 15 5592 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5592) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5592.1, data_15_5592.2]

/-- Complete interval computation for depth 15, residue 5593. -/
theorem bounds_15_5593 : exactInterval 15 5593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5593 : oddCount 5593 15 = 8 ∧ acceleratedOrbit 15 5593 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5593) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5593.1, data_15_5593.2]

/-- Complete interval computation for depth 15, residue 5594. -/
theorem bounds_15_5594 : exactInterval 15 5594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5594 : oddCount 5594 15 = 8 ∧ acceleratedOrbit 15 5594 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5594) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5594.1, data_15_5594.2]

/-- Complete interval computation for depth 15, residue 5595. -/
theorem bounds_15_5595 : exactInterval 15 5595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5595 : oddCount 5595 15 = 6 ∧ acceleratedOrbit 15 5595 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5595) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5595.1, data_15_5595.2]

/-- Complete interval computation for depth 15, residue 5596. -/
theorem bounds_15_5596 : exactInterval 15 5596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5596 : oddCount 5596 15 = 8 ∧ acceleratedOrbit 15 5596 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5596) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5596.1, data_15_5596.2]

/-- Complete interval computation for depth 15, residue 5597. -/
theorem bounds_15_5597 : exactInterval 15 5597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5597 : oddCount 5597 15 = 8 ∧ acceleratedOrbit 15 5597 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5597) = 3 ^ 8 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5597.1, data_15_5597.2]

/-- Complete interval computation for depth 15, residue 5598. -/
theorem bounds_15_5598 : exactInterval 15 5598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5598 : oddCount 5598 15 = 9 ∧ acceleratedOrbit 15 5598 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5598) = 3 ^ 9 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5598.1, data_15_5598.2]

/-- Complete interval computation for depth 15, residue 5599. -/
theorem bounds_15_5599 : exactInterval 15 5599 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5599) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5599 : oddCount 5599 15 = 9 ∧ acceleratedOrbit 15 5599 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5599) = 3 ^ 9 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5599.1, data_15_5599.2]

/-- Complete interval computation for depth 15, residue 5600. -/
theorem bounds_15_5600 : exactInterval 15 5600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5600 : oddCount 5600 15 = 7 ∧ acceleratedOrbit 15 5600 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5600) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5600.1, data_15_5600.2]

/-- Complete interval computation for depth 15, residue 5601. -/
theorem bounds_15_5601 : exactInterval 15 5601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5601 : oddCount 5601 15 = 7 ∧ acceleratedOrbit 15 5601 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5601) = 3 ^ 7 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5601.1, data_15_5601.2]

/-- Complete interval computation for depth 15, residue 5602. -/
theorem bounds_15_5602 : exactInterval 15 5602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5602 : oddCount 5602 15 = 4 ∧ acceleratedOrbit 15 5602 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5602) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5602.1, data_15_5602.2]

end Collatz.Research.PassageAtlas.Batch0171
