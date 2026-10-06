import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0937

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30670. -/
theorem bounds_15_30670 : exactInterval 15 30670 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30670 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30670) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30670 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30670 : oddCount 30670 15 = 8 ∧ acceleratedOrbit 15 30670 = 6142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30670 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30670) = 3 ^ 8 * m + 6142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30670.1, data_15_30670.2]

/-- Complete interval computation for depth 15, residue 30671. -/
theorem bounds_15_30671 : exactInterval 15 30671 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30671 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30671) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30671 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30671 : oddCount 30671 15 = 8 ∧ acceleratedOrbit 15 30671 = 6142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30671 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30671) = 3 ^ 8 * m + 6142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30671.1, data_15_30671.2]

/-- Complete interval computation for depth 15, residue 30672. -/
theorem bounds_15_30672 : exactInterval 15 30672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30672 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30672) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30672 : oddCount 30672 15 = 7 ∧ acceleratedOrbit 15 30672 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30672 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30672) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30672.1, data_15_30672.2]

/-- Complete interval computation for depth 15, residue 30673. -/
theorem bounds_15_30673 : exactInterval 15 30673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30673 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30673) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30673 : oddCount 30673 15 = 6 ∧ acceleratedOrbit 15 30673 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30673 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30673) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30673.1, data_15_30673.2]

/-- Complete interval computation for depth 15, residue 30674. -/
theorem bounds_15_30674 : exactInterval 15 30674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30674 : oddCount 30674 15 = 11 ∧ acceleratedOrbit 15 30674 = 165847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30674) = 3 ^ 11 * m + 165847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30674.1, data_15_30674.2]

/-- Complete interval computation for depth 15, residue 30675. -/
theorem bounds_15_30675 : exactInterval 15 30675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30675 : oddCount 30675 15 = 11 ∧ acceleratedOrbit 15 30675 = 165847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30675) = 3 ^ 11 * m + 165847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30675.1, data_15_30675.2]

/-- Complete interval computation for depth 15, residue 30676. -/
theorem bounds_15_30676 : exactInterval 15 30676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30676 : oddCount 30676 15 = 7 ∧ acceleratedOrbit 15 30676 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30676) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30676.1, data_15_30676.2]

/-- Complete interval computation for depth 15, residue 30677. -/
theorem bounds_15_30677 : exactInterval 15 30677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30677 : oddCount 30677 15 = 7 ∧ acceleratedOrbit 15 30677 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30677) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30677.1, data_15_30677.2]

/-- Complete interval computation for depth 15, residue 30678. -/
theorem bounds_15_30678 : exactInterval 15 30678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30678 : oddCount 30678 15 = 9 ∧ acceleratedOrbit 15 30678 = 18431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30678) = 3 ^ 9 * m + 18431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30678.1, data_15_30678.2]

/-- Complete interval computation for depth 15, residue 30679. -/
theorem bounds_15_30679 : exactInterval 15 30679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30679) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30679 : oddCount 30679 15 = 9 ∧ acceleratedOrbit 15 30679 = 18431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30679) = 3 ^ 9 * m + 18431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30679.1, data_15_30679.2]

/-- Complete interval computation for depth 15, residue 30680. -/
theorem bounds_15_30680 : exactInterval 15 30680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30680 : oddCount 30680 15 = 8 ∧ acceleratedOrbit 15 30680 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30680) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30680.1, data_15_30680.2]

/-- Complete interval computation for depth 15, residue 30681. -/
theorem bounds_15_30681 : exactInterval 15 30681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30681 : oddCount 30681 15 = 7 ∧ acceleratedOrbit 15 30681 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30681) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30681.1, data_15_30681.2]

/-- Complete interval computation for depth 15, residue 30682. -/
theorem bounds_15_30682 : exactInterval 15 30682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30682 : oddCount 30682 15 = 8 ∧ acceleratedOrbit 15 30682 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30682) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30682.1, data_15_30682.2]

/-- Complete interval computation for depth 15, residue 30683. -/
theorem bounds_15_30683 : exactInterval 15 30683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30683 : oddCount 30683 15 = 7 ∧ acceleratedOrbit 15 30683 = 2048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30683) = 3 ^ 7 * m + 2048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30683.1, data_15_30683.2]

/-- Complete interval computation for depth 15, residue 30684. -/
theorem bounds_15_30684 : exactInterval 15 30684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30684 : oddCount 30684 15 = 8 ∧ acceleratedOrbit 15 30684 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30684) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30684.1, data_15_30684.2]

/-- Complete interval computation for depth 15, residue 30685. -/
theorem bounds_15_30685 : exactInterval 15 30685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30685 : oddCount 30685 15 = 8 ∧ acceleratedOrbit 15 30685 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30685) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30685.1, data_15_30685.2]

/-- Complete interval computation for depth 15, residue 30686. -/
theorem bounds_15_30686 : exactInterval 15 30686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30686 : oddCount 30686 15 = 9 ∧ acceleratedOrbit 15 30686 = 18434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30686) = 3 ^ 9 * m + 18434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30686.1, data_15_30686.2]

/-- Complete interval computation for depth 15, residue 30687. -/
theorem bounds_15_30687 : exactInterval 15 30687 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30687) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30687 : oddCount 30687 15 = 9 ∧ acceleratedOrbit 15 30687 = 18434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30687) = 3 ^ 9 * m + 18434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30687.1, data_15_30687.2]

/-- Complete interval computation for depth 15, residue 30688. -/
theorem bounds_15_30688 : exactInterval 15 30688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30688 : oddCount 30688 15 = 8 ∧ acceleratedOrbit 15 30688 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30688) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30688.1, data_15_30688.2]

/-- Complete interval computation for depth 15, residue 30689. -/
theorem bounds_15_30689 : exactInterval 15 30689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30689 : oddCount 30689 15 = 9 ∧ acceleratedOrbit 15 30689 = 18436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30689) = 3 ^ 9 * m + 18436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30689.1, data_15_30689.2]

/-- Complete interval computation for depth 15, residue 30690. -/
theorem bounds_15_30690 : exactInterval 15 30690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30690 : oddCount 30690 15 = 7 ∧ acceleratedOrbit 15 30690 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30690) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30690.1, data_15_30690.2]

/-- Complete interval computation for depth 15, residue 30691. -/
theorem bounds_15_30691 : exactInterval 15 30691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30691 : oddCount 30691 15 = 7 ∧ acceleratedOrbit 15 30691 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30691) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30691.1, data_15_30691.2]

/-- Complete interval computation for depth 15, residue 30692. -/
theorem bounds_15_30692 : exactInterval 15 30692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30692 : oddCount 30692 15 = 6 ∧ acceleratedOrbit 15 30692 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30692) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30692.1, data_15_30692.2]

/-- Complete interval computation for depth 15, residue 30693. -/
theorem bounds_15_30693 : exactInterval 15 30693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30693 : oddCount 30693 15 = 6 ∧ acceleratedOrbit 15 30693 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30693) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30693.1, data_15_30693.2]

/-- Complete interval computation for depth 15, residue 30694. -/
theorem bounds_15_30694 : exactInterval 15 30694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30694 : oddCount 30694 15 = 6 ∧ acceleratedOrbit 15 30694 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30694) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30694.1, data_15_30694.2]

/-- Complete interval computation for depth 15, residue 30695. -/
theorem bounds_15_30695 : exactInterval 15 30695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30695 : oddCount 30695 15 = 9 ∧ acceleratedOrbit 15 30695 = 18440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30695) = 3 ^ 9 * m + 18440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30695.1, data_15_30695.2]

/-- Complete interval computation for depth 15, residue 30696. -/
theorem bounds_15_30696 : exactInterval 15 30696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30696 : oddCount 30696 15 = 8 ∧ acceleratedOrbit 15 30696 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30696) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30696.1, data_15_30696.2]

/-- Complete interval computation for depth 15, residue 30697. -/
theorem bounds_15_30697 : exactInterval 15 30697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30697 : oddCount 30697 15 = 11 ∧ acceleratedOrbit 15 30697 = 165962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30697) = 3 ^ 11 * m + 165962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30697.1, data_15_30697.2]

/-- Complete interval computation for depth 15, residue 30698. -/
theorem bounds_15_30698 : exactInterval 15 30698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30698 : oddCount 30698 15 = 8 ∧ acceleratedOrbit 15 30698 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30698) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30698.1, data_15_30698.2]

/-- Complete interval computation for depth 15, residue 30699. -/
theorem bounds_15_30699 : exactInterval 15 30699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30699 : oddCount 30699 15 = 10 ∧ acceleratedOrbit 15 30699 = 55325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30699) = 3 ^ 10 * m + 55325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30699.1, data_15_30699.2]

/-- Complete interval computation for depth 15, residue 30700. -/
theorem bounds_15_30700 : exactInterval 15 30700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30700 : oddCount 30700 15 = 8 ∧ acceleratedOrbit 15 30700 = 6149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30700) = 3 ^ 8 * m + 6149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30700.1, data_15_30700.2]

/-- Complete interval computation for depth 15, residue 30701. -/
theorem bounds_15_30701 : exactInterval 15 30701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30701 : oddCount 30701 15 = 8 ∧ acceleratedOrbit 15 30701 = 6149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30701) = 3 ^ 8 * m + 6149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30701.1, data_15_30701.2]

/-- Complete interval computation for depth 15, residue 30702. -/
theorem bounds_15_30702 : exactInterval 15 30702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30702 : oddCount 30702 15 = 8 ∧ acceleratedOrbit 15 30702 = 6149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30702) = 3 ^ 8 * m + 6149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30702.1, data_15_30702.2]

end Collatz.Research.PassageAtlas.Batch0937
