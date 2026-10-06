import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0232

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7569. -/
theorem bounds_15_7569 : exactInterval 15 7569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7569 : oddCount 7569 15 = 7 ∧ acceleratedOrbit 15 7569 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7569) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7569.1, data_15_7569.2]

/-- Complete interval computation for depth 15, residue 7570. -/
theorem bounds_15_7570 : exactInterval 15 7570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7570 : oddCount 7570 15 = 7 ∧ acceleratedOrbit 15 7570 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7570) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7570.1, data_15_7570.2]

/-- Complete interval computation for depth 15, residue 7571. -/
theorem bounds_15_7571 : exactInterval 15 7571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7571 : oddCount 7571 15 = 7 ∧ acceleratedOrbit 15 7571 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7571) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7571.1, data_15_7571.2]

/-- Complete interval computation for depth 15, residue 7572. -/
theorem bounds_15_7572 : exactInterval 15 7572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7572 : oddCount 7572 15 = 4 ∧ acceleratedOrbit 15 7572 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7572) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7572.1, data_15_7572.2]

/-- Complete interval computation for depth 15, residue 7573. -/
theorem bounds_15_7573 : exactInterval 15 7573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7573 : oddCount 7573 15 = 4 ∧ acceleratedOrbit 15 7573 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7573) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7573.1, data_15_7573.2]

/-- Complete interval computation for depth 15, residue 7574. -/
theorem bounds_15_7574 : exactInterval 15 7574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7574 : oddCount 7574 15 = 9 ∧ acceleratedOrbit 15 7574 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7574) = 3 ^ 9 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7574.1, data_15_7574.2]

/-- Complete interval computation for depth 15, residue 7575. -/
theorem bounds_15_7575 : exactInterval 15 7575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7575 : oddCount 7575 15 = 9 ∧ acceleratedOrbit 15 7575 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7575) = 3 ^ 9 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7575.1, data_15_7575.2]

/-- Complete interval computation for depth 15, residue 7576. -/
theorem bounds_15_7576 : exactInterval 15 7576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7576 : oddCount 7576 15 = 4 ∧ acceleratedOrbit 15 7576 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7576) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7576.1, data_15_7576.2]

/-- Complete interval computation for depth 15, residue 7577. -/
theorem bounds_15_7577 : exactInterval 15 7577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7577 : oddCount 7577 15 = 9 ∧ acceleratedOrbit 15 7577 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7577) = 3 ^ 9 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7577.1, data_15_7577.2]

/-- Complete interval computation for depth 15, residue 7578. -/
theorem bounds_15_7578 : exactInterval 15 7578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7578 : oddCount 7578 15 = 4 ∧ acceleratedOrbit 15 7578 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7578) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7578.1, data_15_7578.2]

/-- Complete interval computation for depth 15, residue 7579. -/
theorem bounds_15_7579 : exactInterval 15 7579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7579 : oddCount 7579 15 = 11 ∧ acceleratedOrbit 15 7579 = 40985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7579) = 3 ^ 11 * m + 40985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7579.1, data_15_7579.2]

/-- Complete interval computation for depth 15, residue 7580. -/
theorem bounds_15_7580 : exactInterval 15 7580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7580 : oddCount 7580 15 = 11 ∧ acceleratedOrbit 15 7580 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7580) = 3 ^ 11 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7580.1, data_15_7580.2]

/-- Complete interval computation for depth 15, residue 7581. -/
theorem bounds_15_7581 : exactInterval 15 7581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7581 : oddCount 7581 15 = 11 ∧ acceleratedOrbit 15 7581 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7581) = 3 ^ 11 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7581.1, data_15_7581.2]

/-- Complete interval computation for depth 15, residue 7582. -/
theorem bounds_15_7582 : exactInterval 15 7582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7582 : oddCount 7582 15 = 11 ∧ acceleratedOrbit 15 7582 = 41006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7582) = 3 ^ 11 * m + 41006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7582.1, data_15_7582.2]

/-- Complete interval computation for depth 15, residue 7583. -/
theorem bounds_15_7583 : exactInterval 15 7583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7583 : oddCount 7583 15 = 10 ∧ acceleratedOrbit 15 7583 = 13667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7583) = 3 ^ 10 * m + 13667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7583.1, data_15_7583.2]

/-- Complete interval computation for depth 15, residue 7584. -/
theorem bounds_15_7584 : exactInterval 15 7584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7584 : oddCount 7584 15 = 4 ∧ acceleratedOrbit 15 7584 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7584) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7584.1, data_15_7584.2]

/-- Complete interval computation for depth 15, residue 7585. -/
theorem bounds_15_7585 : exactInterval 15 7585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7585 : oddCount 7585 15 = 8 ∧ acceleratedOrbit 15 7585 = 1520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7585) = 3 ^ 8 * m + 1520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7585.1, data_15_7585.2]

/-- Complete interval computation for depth 15, residue 7586. -/
theorem bounds_15_7586 : exactInterval 15 7586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7586 : oddCount 7586 15 = 6 ∧ acceleratedOrbit 15 7586 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7586) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7586.1, data_15_7586.2]

/-- Complete interval computation for depth 15, residue 7587. -/
theorem bounds_15_7587 : exactInterval 15 7587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7587 : oddCount 7587 15 = 6 ∧ acceleratedOrbit 15 7587 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7587) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7587.1, data_15_7587.2]

/-- Complete interval computation for depth 15, residue 7588. -/
theorem bounds_15_7588 : exactInterval 15 7588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7588 : oddCount 7588 15 = 6 ∧ acceleratedOrbit 15 7588 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7588) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7588.1, data_15_7588.2]

/-- Complete interval computation for depth 15, residue 7589. -/
theorem bounds_15_7589 : exactInterval 15 7589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7589 : oddCount 7589 15 = 6 ∧ acceleratedOrbit 15 7589 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7589) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7589.1, data_15_7589.2]

/-- Complete interval computation for depth 15, residue 7590. -/
theorem bounds_15_7590 : exactInterval 15 7590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7590 : oddCount 7590 15 = 6 ∧ acceleratedOrbit 15 7590 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7590) = 3 ^ 6 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7590.1, data_15_7590.2]

/-- Complete interval computation for depth 15, residue 7591. -/
theorem bounds_15_7591 : exactInterval 15 7591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7591 : oddCount 7591 15 = 9 ∧ acceleratedOrbit 15 7591 = 4562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7591) = 3 ^ 9 * m + 4562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7591.1, data_15_7591.2]

/-- Complete interval computation for depth 15, residue 7592. -/
theorem bounds_15_7592 : exactInterval 15 7592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7592 : oddCount 7592 15 = 4 ∧ acceleratedOrbit 15 7592 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7592) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7592.1, data_15_7592.2]

/-- Complete interval computation for depth 15, residue 7593. -/
theorem bounds_15_7593 : exactInterval 15 7593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7593 : oddCount 7593 15 = 10 ∧ acceleratedOrbit 15 7593 = 13688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7593) = 3 ^ 10 * m + 13688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7593.1, data_15_7593.2]

/-- Complete interval computation for depth 15, residue 7594. -/
theorem bounds_15_7594 : exactInterval 15 7594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7594 : oddCount 7594 15 = 4 ∧ acceleratedOrbit 15 7594 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7594) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7594.1, data_15_7594.2]

/-- Complete interval computation for depth 15, residue 7595. -/
theorem bounds_15_7595 : exactInterval 15 7595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7595 : oddCount 7595 15 = 9 ∧ acceleratedOrbit 15 7595 = 4564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7595) = 3 ^ 9 * m + 4564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7595.1, data_15_7595.2]

/-- Complete interval computation for depth 15, residue 7596. -/
theorem bounds_15_7596 : exactInterval 15 7596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7596 : oddCount 7596 15 = 7 ∧ acceleratedOrbit 15 7596 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7596) = 3 ^ 7 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7596.1, data_15_7596.2]

/-- Complete interval computation for depth 15, residue 7597. -/
theorem bounds_15_7597 : exactInterval 15 7597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7597 : oddCount 7597 15 = 7 ∧ acceleratedOrbit 15 7597 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7597) = 3 ^ 7 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7597.1, data_15_7597.2]

/-- Complete interval computation for depth 15, residue 7598. -/
theorem bounds_15_7598 : exactInterval 15 7598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7598 : oddCount 7598 15 = 7 ∧ acceleratedOrbit 15 7598 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7598) = 3 ^ 7 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7598.1, data_15_7598.2]

/-- Complete interval computation for depth 15, residue 7599. -/
theorem bounds_15_7599 : exactInterval 15 7599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7599 : oddCount 7599 15 = 8 ∧ acceleratedOrbit 15 7599 = 1522 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7599) = 3 ^ 8 * m + 1522 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7599.1, data_15_7599.2]

/-- Complete interval computation for depth 15, residue 7600. -/
theorem bounds_15_7600 : exactInterval 15 7600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7600 : oddCount 7600 15 = 6 ∧ acceleratedOrbit 15 7600 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7600) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7600.1, data_15_7600.2]

/-- Complete interval computation for depth 15, residue 7601. -/
theorem bounds_15_7601 : exactInterval 15 7601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7601 : oddCount 7601 15 = 6 ∧ acceleratedOrbit 15 7601 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7601) = 3 ^ 6 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7601.1, data_15_7601.2]

end Collatz.Research.PassageAtlas.Batch0232
