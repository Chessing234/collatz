import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0388

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12681. -/
theorem bounds_15_12681 : exactInterval 15 12681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12681 : oddCount 12681 15 = 8 ∧ acceleratedOrbit 15 12681 = 2540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12681) = 3 ^ 8 * m + 2540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12681.1, data_15_12681.2]

/-- Complete interval computation for depth 15, residue 12682. -/
theorem bounds_15_12682 : exactInterval 15 12682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12682 : oddCount 12682 15 = 7 ∧ acceleratedOrbit 15 12682 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12682) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12682.1, data_15_12682.2]

/-- Complete interval computation for depth 15, residue 12683. -/
theorem bounds_15_12683 : exactInterval 15 12683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12683 : oddCount 12683 15 = 10 ∧ acceleratedOrbit 15 12683 = 22862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12683) = 3 ^ 10 * m + 22862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12683.1, data_15_12683.2]

/-- Complete interval computation for depth 15, residue 12684. -/
theorem bounds_15_12684 : exactInterval 15 12684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12684 : oddCount 12684 15 = 7 ∧ acceleratedOrbit 15 12684 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12684) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12684.1, data_15_12684.2]

/-- Complete interval computation for depth 15, residue 12685. -/
theorem bounds_15_12685 : exactInterval 15 12685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12685 : oddCount 12685 15 = 7 ∧ acceleratedOrbit 15 12685 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12685) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12685.1, data_15_12685.2]

/-- Complete interval computation for depth 15, residue 12686. -/
theorem bounds_15_12686 : exactInterval 15 12686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12686 : oddCount 12686 15 = 7 ∧ acceleratedOrbit 15 12686 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12686) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12686.1, data_15_12686.2]

/-- Complete interval computation for depth 15, residue 12687. -/
theorem bounds_15_12687 : exactInterval 15 12687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12687 : oddCount 12687 15 = 7 ∧ acceleratedOrbit 15 12687 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12687) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12687.1, data_15_12687.2]

/-- Complete interval computation for depth 15, residue 12688. -/
theorem bounds_15_12688 : exactInterval 15 12688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12688 : oddCount 12688 15 = 7 ∧ acceleratedOrbit 15 12688 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12688) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12688.1, data_15_12688.2]

/-- Complete interval computation for depth 15, residue 12689. -/
theorem bounds_15_12689 : exactInterval 15 12689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12689 : oddCount 12689 15 = 6 ∧ acceleratedOrbit 15 12689 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12689) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12689.1, data_15_12689.2]

/-- Complete interval computation for depth 15, residue 12690. -/
theorem bounds_15_12690 : exactInterval 15 12690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12690 : oddCount 12690 15 = 6 ∧ acceleratedOrbit 15 12690 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12690) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12690.1, data_15_12690.2]

/-- Complete interval computation for depth 15, residue 12691. -/
theorem bounds_15_12691 : exactInterval 15 12691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12691 : oddCount 12691 15 = 6 ∧ acceleratedOrbit 15 12691 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12691) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12691.1, data_15_12691.2]

/-- Complete interval computation for depth 15, residue 12692. -/
theorem bounds_15_12692 : exactInterval 15 12692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12692 : oddCount 12692 15 = 7 ∧ acceleratedOrbit 15 12692 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12692) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12692.1, data_15_12692.2]

/-- Complete interval computation for depth 15, residue 12693. -/
theorem bounds_15_12693 : exactInterval 15 12693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12693 : oddCount 12693 15 = 7 ∧ acceleratedOrbit 15 12693 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12693) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12693.1, data_15_12693.2]

/-- Complete interval computation for depth 15, residue 12694. -/
theorem bounds_15_12694 : exactInterval 15 12694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12694 : oddCount 12694 15 = 7 ∧ acceleratedOrbit 15 12694 = 848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12694) = 3 ^ 7 * m + 848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12694.1, data_15_12694.2]

/-- Complete interval computation for depth 15, residue 12695. -/
theorem bounds_15_12695 : exactInterval 15 12695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12695 : oddCount 12695 15 = 7 ∧ acceleratedOrbit 15 12695 = 848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12695) = 3 ^ 7 * m + 848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12695.1, data_15_12695.2]

/-- Complete interval computation for depth 15, residue 12696. -/
theorem bounds_15_12696 : exactInterval 15 12696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12696 : oddCount 12696 15 = 7 ∧ acceleratedOrbit 15 12696 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12696) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12696.1, data_15_12696.2]

/-- Complete interval computation for depth 15, residue 12697. -/
theorem bounds_15_12697 : exactInterval 15 12697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12697 : oddCount 12697 15 = 7 ∧ acceleratedOrbit 15 12697 = 848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12697) = 3 ^ 7 * m + 848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12697.1, data_15_12697.2]

/-- Complete interval computation for depth 15, residue 12698. -/
theorem bounds_15_12698 : exactInterval 15 12698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12698 : oddCount 12698 15 = 7 ∧ acceleratedOrbit 15 12698 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12698) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12698.1, data_15_12698.2]

/-- Complete interval computation for depth 15, residue 12699. -/
theorem bounds_15_12699 : exactInterval 15 12699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12699 : oddCount 12699 15 = 8 ∧ acceleratedOrbit 15 12699 = 2543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12699) = 3 ^ 8 * m + 2543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12699.1, data_15_12699.2]

/-- Complete interval computation for depth 15, residue 12700. -/
theorem bounds_15_12700 : exactInterval 15 12700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12700 : oddCount 12700 15 = 11 ∧ acceleratedOrbit 15 12700 = 68687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12700) = 3 ^ 11 * m + 68687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12700.1, data_15_12700.2]

/-- Complete interval computation for depth 15, residue 12701. -/
theorem bounds_15_12701 : exactInterval 15 12701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12701 : oddCount 12701 15 = 11 ∧ acceleratedOrbit 15 12701 = 68687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12701) = 3 ^ 11 * m + 68687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12701.1, data_15_12701.2]

/-- Complete interval computation for depth 15, residue 12702. -/
theorem bounds_15_12702 : exactInterval 15 12702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12702 : oddCount 12702 15 = 11 ∧ acceleratedOrbit 15 12702 = 68687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12702) = 3 ^ 11 * m + 68687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12702.1, data_15_12702.2]

/-- Complete interval computation for depth 15, residue 12703. -/
theorem bounds_15_12703 : exactInterval 15 12703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12703 : oddCount 12703 15 = 11 ∧ acceleratedOrbit 15 12703 = 68681 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12703) = 3 ^ 11 * m + 68681 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12703.1, data_15_12703.2]

/-- Complete interval computation for depth 15, residue 12704. -/
theorem bounds_15_12704 : exactInterval 15 12704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12704 : oddCount 12704 15 = 3 ∧ acceleratedOrbit 15 12704 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12704) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12704.1, data_15_12704.2]

/-- Complete interval computation for depth 15, residue 12705. -/
theorem bounds_15_12705 : exactInterval 15 12705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12705 : oddCount 12705 15 = 9 ∧ acceleratedOrbit 15 12705 = 7634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12705) = 3 ^ 9 * m + 7634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12705.1, data_15_12705.2]

/-- Complete interval computation for depth 15, residue 12706. -/
theorem bounds_15_12706 : exactInterval 15 12706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12706 : oddCount 12706 15 = 9 ∧ acceleratedOrbit 15 12706 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12706) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12706.1, data_15_12706.2]

/-- Complete interval computation for depth 15, residue 12707. -/
theorem bounds_15_12707 : exactInterval 15 12707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12707 : oddCount 12707 15 = 9 ∧ acceleratedOrbit 15 12707 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12707) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12707.1, data_15_12707.2]

/-- Complete interval computation for depth 15, residue 12708. -/
theorem bounds_15_12708 : exactInterval 15 12708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12708 : oddCount 12708 15 = 9 ∧ acceleratedOrbit 15 12708 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12708) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12708.1, data_15_12708.2]

/-- Complete interval computation for depth 15, residue 12709. -/
theorem bounds_15_12709 : exactInterval 15 12709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12709 : oddCount 12709 15 = 9 ∧ acceleratedOrbit 15 12709 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12709) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12709.1, data_15_12709.2]

/-- Complete interval computation for depth 15, residue 12710. -/
theorem bounds_15_12710 : exactInterval 15 12710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12710 : oddCount 12710 15 = 9 ∧ acceleratedOrbit 15 12710 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12710) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12710.1, data_15_12710.2]

/-- Complete interval computation for depth 15, residue 12711. -/
theorem bounds_15_12711 : exactInterval 15 12711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12711 : oddCount 12711 15 = 8 ∧ acceleratedOrbit 15 12711 = 2546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12711) = 3 ^ 8 * m + 2546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12711.1, data_15_12711.2]

/-- Complete interval computation for depth 15, residue 12712. -/
theorem bounds_15_12712 : exactInterval 15 12712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12712 : oddCount 12712 15 = 3 ∧ acceleratedOrbit 15 12712 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12712) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12712.1, data_15_12712.2]

end Collatz.Research.PassageAtlas.Batch0388
