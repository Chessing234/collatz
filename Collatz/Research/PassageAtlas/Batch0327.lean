import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0327

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10682. -/
theorem bounds_15_10682 : exactInterval 15 10682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10682 : oddCount 10682 15 = 9 ∧ acceleratedOrbit 15 10682 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10682) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10682.1, data_15_10682.2]

/-- Complete interval computation for depth 15, residue 10683. -/
theorem bounds_15_10683 : exactInterval 15 10683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10683 : oddCount 10683 15 = 9 ∧ acceleratedOrbit 15 10683 = 6419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10683) = 3 ^ 9 * m + 6419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10683.1, data_15_10683.2]

/-- Complete interval computation for depth 15, residue 10684. -/
theorem bounds_15_10684 : exactInterval 15 10684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10684 : oddCount 10684 15 = 9 ∧ acceleratedOrbit 15 10684 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10684) = 3 ^ 9 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10684.1, data_15_10684.2]

/-- Complete interval computation for depth 15, residue 10685. -/
theorem bounds_15_10685 : exactInterval 15 10685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10685 : oddCount 10685 15 = 9 ∧ acceleratedOrbit 15 10685 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10685) = 3 ^ 9 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10685.1, data_15_10685.2]

/-- Complete interval computation for depth 15, residue 10686. -/
theorem bounds_15_10686 : exactInterval 15 10686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10686 : oddCount 10686 15 = 9 ∧ acceleratedOrbit 15 10686 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10686) = 3 ^ 9 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10686.1, data_15_10686.2]

/-- Complete interval computation for depth 15, residue 10687. -/
theorem bounds_15_10687 : exactInterval 15 10687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10687 : oddCount 10687 15 = 11 ∧ acceleratedOrbit 15 10687 = 57781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10687) = 3 ^ 11 * m + 57781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10687.1, data_15_10687.2]

/-- Complete interval computation for depth 15, residue 10688. -/
theorem bounds_15_10688 : exactInterval 15 10688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10688 : oddCount 10688 15 = 7 ∧ acceleratedOrbit 15 10688 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10688) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10688.1, data_15_10688.2]

/-- Complete interval computation for depth 15, residue 10689. -/
theorem bounds_15_10689 : exactInterval 15 10689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10689 : oddCount 10689 15 = 9 ∧ acceleratedOrbit 15 10689 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10689) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10689.1, data_15_10689.2]

/-- Complete interval computation for depth 15, residue 10690. -/
theorem bounds_15_10690 : exactInterval 15 10690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10690 : oddCount 10690 15 = 10 ∧ acceleratedOrbit 15 10690 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10690) = 3 ^ 10 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10690.1, data_15_10690.2]

/-- Complete interval computation for depth 15, residue 10691. -/
theorem bounds_15_10691 : exactInterval 15 10691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10691 : oddCount 10691 15 = 10 ∧ acceleratedOrbit 15 10691 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10691) = 3 ^ 10 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10691.1, data_15_10691.2]

/-- Complete interval computation for depth 15, residue 10692. -/
theorem bounds_15_10692 : exactInterval 15 10692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10692 : oddCount 10692 15 = 6 ∧ acceleratedOrbit 15 10692 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10692) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10692.1, data_15_10692.2]

/-- Complete interval computation for depth 15, residue 10693. -/
theorem bounds_15_10693 : exactInterval 15 10693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10693 : oddCount 10693 15 = 6 ∧ acceleratedOrbit 15 10693 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10693) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10693.1, data_15_10693.2]

/-- Complete interval computation for depth 15, residue 10694. -/
theorem bounds_15_10694 : exactInterval 15 10694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10694 : oddCount 10694 15 = 6 ∧ acceleratedOrbit 15 10694 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10694) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10694.1, data_15_10694.2]

/-- Complete interval computation for depth 15, residue 10695. -/
theorem bounds_15_10695 : exactInterval 15 10695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10695 : oddCount 10695 15 = 11 ∧ acceleratedOrbit 15 10695 = 57833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10695) = 3 ^ 11 * m + 57833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10695.1, data_15_10695.2]

/-- Complete interval computation for depth 15, residue 10696. -/
theorem bounds_15_10696 : exactInterval 15 10696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10696 : oddCount 10696 15 = 8 ∧ acceleratedOrbit 15 10696 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10696) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10696.1, data_15_10696.2]

/-- Complete interval computation for depth 15, residue 10697. -/
theorem bounds_15_10697 : exactInterval 15 10697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10697 : oddCount 10697 15 = 8 ∧ acceleratedOrbit 15 10697 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10697) = 3 ^ 8 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10697.1, data_15_10697.2]

/-- Complete interval computation for depth 15, residue 10698. -/
theorem bounds_15_10698 : exactInterval 15 10698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10698 : oddCount 10698 15 = 8 ∧ acceleratedOrbit 15 10698 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10698) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10698.1, data_15_10698.2]

/-- Complete interval computation for depth 15, residue 10699. -/
theorem bounds_15_10699 : exactInterval 15 10699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10699 : oddCount 10699 15 = 7 ∧ acceleratedOrbit 15 10699 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10699) = 3 ^ 7 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10699.1, data_15_10699.2]

/-- Complete interval computation for depth 15, residue 10700. -/
theorem bounds_15_10700 : exactInterval 15 10700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10700 : oddCount 10700 15 = 8 ∧ acceleratedOrbit 15 10700 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10700) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10700.1, data_15_10700.2]

/-- Complete interval computation for depth 15, residue 10701. -/
theorem bounds_15_10701 : exactInterval 15 10701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10701 : oddCount 10701 15 = 8 ∧ acceleratedOrbit 15 10701 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10701) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10701.1, data_15_10701.2]

/-- Complete interval computation for depth 15, residue 10702. -/
theorem bounds_15_10702 : exactInterval 15 10702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10702 : oddCount 10702 15 = 10 ∧ acceleratedOrbit 15 10702 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10702) = 3 ^ 10 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10702.1, data_15_10702.2]

/-- Complete interval computation for depth 15, residue 10703. -/
theorem bounds_15_10703 : exactInterval 15 10703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10703 : oddCount 10703 15 = 10 ∧ acceleratedOrbit 15 10703 = 19291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10703) = 3 ^ 10 * m + 19291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10703.1, data_15_10703.2]

/-- Complete interval computation for depth 15, residue 10704. -/
theorem bounds_15_10704 : exactInterval 15 10704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10704 : oddCount 10704 15 = 7 ∧ acceleratedOrbit 15 10704 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10704) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10704.1, data_15_10704.2]

/-- Complete interval computation for depth 15, residue 10705. -/
theorem bounds_15_10705 : exactInterval 15 10705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10705 : oddCount 10705 15 = 8 ∧ acceleratedOrbit 15 10705 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10705) = 3 ^ 8 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10705.1, data_15_10705.2]

/-- Complete interval computation for depth 15, residue 10706. -/
theorem bounds_15_10706 : exactInterval 15 10706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10706 : oddCount 10706 15 = 7 ∧ acceleratedOrbit 15 10706 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10706) = 3 ^ 7 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10706.1, data_15_10706.2]

/-- Complete interval computation for depth 15, residue 10707. -/
theorem bounds_15_10707 : exactInterval 15 10707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10707 : oddCount 10707 15 = 7 ∧ acceleratedOrbit 15 10707 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10707) = 3 ^ 7 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10707.1, data_15_10707.2]

/-- Complete interval computation for depth 15, residue 10708. -/
theorem bounds_15_10708 : exactInterval 15 10708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10708 : oddCount 10708 15 = 7 ∧ acceleratedOrbit 15 10708 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10708) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10708.1, data_15_10708.2]

/-- Complete interval computation for depth 15, residue 10709. -/
theorem bounds_15_10709 : exactInterval 15 10709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10709 : oddCount 10709 15 = 7 ∧ acceleratedOrbit 15 10709 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10709) = 3 ^ 7 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10709.1, data_15_10709.2]

/-- Complete interval computation for depth 15, residue 10710. -/
theorem bounds_15_10710 : exactInterval 15 10710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10710 : oddCount 10710 15 = 9 ∧ acceleratedOrbit 15 10710 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10710) = 3 ^ 9 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10710.1, data_15_10710.2]

/-- Complete interval computation for depth 15, residue 10711. -/
theorem bounds_15_10711 : exactInterval 15 10711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10711 : oddCount 10711 15 = 9 ∧ acceleratedOrbit 15 10711 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10711) = 3 ^ 9 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10711.1, data_15_10711.2]

/-- Complete interval computation for depth 15, residue 10712. -/
theorem bounds_15_10712 : exactInterval 15 10712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10712 : oddCount 10712 15 = 5 ∧ acceleratedOrbit 15 10712 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10712) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10712.1, data_15_10712.2]

/-- Complete interval computation for depth 15, residue 10713. -/
theorem bounds_15_10713 : exactInterval 15 10713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10713 : oddCount 10713 15 = 5 ∧ acceleratedOrbit 15 10713 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10713) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10713.1, data_15_10713.2]

/-- Complete interval computation for depth 15, residue 10714. -/
theorem bounds_15_10714 : exactInterval 15 10714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10714 : oddCount 10714 15 = 5 ∧ acceleratedOrbit 15 10714 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10714) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10714.1, data_15_10714.2]

end Collatz.Research.PassageAtlas.Batch0327
