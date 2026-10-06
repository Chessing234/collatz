import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0961

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7577. -/
theorem bounds_13_7577 : exactInterval 13 7577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7577 : oddCount 7577 13 = 8 ∧ acceleratedOrbit 13 7577 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7577) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7577.1, data_13_7577.2]

/-- Complete interval computation for depth 13, residue 7578. -/
theorem bounds_13_7578 : exactInterval 13 7578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7578 : oddCount 7578 13 = 3 ∧ acceleratedOrbit 13 7578 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7578) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7578.1, data_13_7578.2]

/-- Complete interval computation for depth 13, residue 7579. -/
theorem bounds_13_7579 : exactInterval 13 7579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7579 : oddCount 7579 13 = 9 ∧ acceleratedOrbit 13 7579 = 18215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7579) = 3 ^ 9 * m + 18215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7579.1, data_13_7579.2]

/-- Complete interval computation for depth 13, residue 7580. -/
theorem bounds_13_7580 : exactInterval 13 7580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7580 : oddCount 7580 13 = 10 ∧ acceleratedOrbit 13 7580 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7580) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7580.1, data_13_7580.2]

/-- Complete interval computation for depth 13, residue 7581. -/
theorem bounds_13_7581 : exactInterval 13 7581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7581 : oddCount 7581 13 = 10 ∧ acceleratedOrbit 13 7581 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7581) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7581.1, data_13_7581.2]

/-- Complete interval computation for depth 13, residue 7582. -/
theorem bounds_13_7582 : exactInterval 13 7582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7582 : oddCount 7582 13 = 10 ∧ acceleratedOrbit 13 7582 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7582) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7582.1, data_13_7582.2]

/-- Complete interval computation for depth 13, residue 7583. -/
theorem bounds_13_7583 : exactInterval 13 7583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7583 : oddCount 7583 13 = 10 ∧ acceleratedOrbit 13 7583 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7583) = 3 ^ 10 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7583.1, data_13_7583.2]

/-- Complete interval computation for depth 13, residue 7584. -/
theorem bounds_13_7584 : exactInterval 13 7584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7584 : oddCount 7584 13 = 4 ∧ acceleratedOrbit 13 7584 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7584) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7584.1, data_13_7584.2]

/-- Complete interval computation for depth 13, residue 7585. -/
theorem bounds_13_7585 : exactInterval 13 7585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7585 : oddCount 7585 13 = 7 ∧ acceleratedOrbit 13 7585 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7585) = 3 ^ 7 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7585.1, data_13_7585.2]

/-- Complete interval computation for depth 13, residue 7586. -/
theorem bounds_13_7586 : exactInterval 13 7586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7586 : oddCount 7586 13 = 6 ∧ acceleratedOrbit 13 7586 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7586) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7586.1, data_13_7586.2]

/-- Complete interval computation for depth 13, residue 7587. -/
theorem bounds_13_7587 : exactInterval 13 7587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7587 : oddCount 7587 13 = 6 ∧ acceleratedOrbit 13 7587 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7587) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7587.1, data_13_7587.2]

/-- Complete interval computation for depth 13, residue 7588. -/
theorem bounds_13_7588 : exactInterval 13 7588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7588 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7588) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7588 : oddCount 7588 13 = 6 ∧ acceleratedOrbit 13 7588 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7588 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7588) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7588.1, data_13_7588.2]

/-- Complete interval computation for depth 13, residue 7589. -/
theorem bounds_13_7589 : exactInterval 13 7589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7589 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7589) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7589 : oddCount 7589 13 = 6 ∧ acceleratedOrbit 13 7589 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7589 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7589) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7589.1, data_13_7589.2]

/-- Complete interval computation for depth 13, residue 7590. -/
theorem bounds_13_7590 : exactInterval 13 7590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7590 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7590) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7590 : oddCount 7590 13 = 6 ∧ acceleratedOrbit 13 7590 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7590 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7590) = 3 ^ 6 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7590.1, data_13_7590.2]

/-- Complete interval computation for depth 13, residue 7591. -/
theorem bounds_13_7591 : exactInterval 13 7591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7591 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7591) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7591 : oddCount 7591 13 = 7 ∧ acceleratedOrbit 13 7591 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7591 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7591) = 3 ^ 7 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7591.1, data_13_7591.2]

end Collatz.Research.StoppingAtlas.Batch0961
