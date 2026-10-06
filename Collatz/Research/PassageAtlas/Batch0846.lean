import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0846

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27688. -/
theorem bounds_15_27688 : exactInterval 15 27688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27688 : oddCount 27688 15 = 7 ∧ acceleratedOrbit 15 27688 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27688) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27688.1, data_15_27688.2]

/-- Complete interval computation for depth 15, residue 27689. -/
theorem bounds_15_27689 : exactInterval 15 27689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27689 : oddCount 27689 15 = 9 ∧ acceleratedOrbit 15 27689 = 16634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27689) = 3 ^ 9 * m + 16634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27689.1, data_15_27689.2]

/-- Complete interval computation for depth 15, residue 27690. -/
theorem bounds_15_27690 : exactInterval 15 27690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27690 : oddCount 27690 15 = 7 ∧ acceleratedOrbit 15 27690 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27690) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27690.1, data_15_27690.2]

/-- Complete interval computation for depth 15, residue 27691. -/
theorem bounds_15_27691 : exactInterval 15 27691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27691 : oddCount 27691 15 = 7 ∧ acceleratedOrbit 15 27691 = 1849 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27691) = 3 ^ 7 * m + 1849 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27691.1, data_15_27691.2]

/-- Complete interval computation for depth 15, residue 27692. -/
theorem bounds_15_27692 : exactInterval 15 27692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27692 : oddCount 27692 15 = 8 ∧ acceleratedOrbit 15 27692 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27692) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27692.1, data_15_27692.2]

/-- Complete interval computation for depth 15, residue 27693. -/
theorem bounds_15_27693 : exactInterval 15 27693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27693 : oddCount 27693 15 = 8 ∧ acceleratedOrbit 15 27693 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27693) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27693.1, data_15_27693.2]

/-- Complete interval computation for depth 15, residue 27694. -/
theorem bounds_15_27694 : exactInterval 15 27694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27694 : oddCount 27694 15 = 8 ∧ acceleratedOrbit 15 27694 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27694) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27694.1, data_15_27694.2]

/-- Complete interval computation for depth 15, residue 27695. -/
theorem bounds_15_27695 : exactInterval 15 27695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27695 : oddCount 27695 15 = 8 ∧ acceleratedOrbit 15 27695 = 5546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27695) = 3 ^ 8 * m + 5546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27695.1, data_15_27695.2]

/-- Complete interval computation for depth 15, residue 27696. -/
theorem bounds_15_27696 : exactInterval 15 27696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27696 : oddCount 27696 15 = 7 ∧ acceleratedOrbit 15 27696 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27696) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27696.1, data_15_27696.2]

/-- Complete interval computation for depth 15, residue 27697. -/
theorem bounds_15_27697 : exactInterval 15 27697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27697 : oddCount 27697 15 = 8 ∧ acceleratedOrbit 15 27697 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27697) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27697.1, data_15_27697.2]

/-- Complete interval computation for depth 15, residue 27698. -/
theorem bounds_15_27698 : exactInterval 15 27698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27698 : oddCount 27698 15 = 8 ∧ acceleratedOrbit 15 27698 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27698) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27698.1, data_15_27698.2]

/-- Complete interval computation for depth 15, residue 27699. -/
theorem bounds_15_27699 : exactInterval 15 27699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27699 : oddCount 27699 15 = 8 ∧ acceleratedOrbit 15 27699 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27699) = 3 ^ 8 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27699.1, data_15_27699.2]

/-- Complete interval computation for depth 15, residue 27700. -/
theorem bounds_15_27700 : exactInterval 15 27700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27700 : oddCount 27700 15 = 7 ∧ acceleratedOrbit 15 27700 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27700) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27700.1, data_15_27700.2]

/-- Complete interval computation for depth 15, residue 27701. -/
theorem bounds_15_27701 : exactInterval 15 27701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27701 : oddCount 27701 15 = 7 ∧ acceleratedOrbit 15 27701 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27701) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27701.1, data_15_27701.2]

/-- Complete interval computation for depth 15, residue 27702. -/
theorem bounds_15_27702 : exactInterval 15 27702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27702 : oddCount 27702 15 = 9 ∧ acceleratedOrbit 15 27702 = 16642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27702) = 3 ^ 9 * m + 16642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27702.1, data_15_27702.2]

/-- Complete interval computation for depth 15, residue 27703. -/
theorem bounds_15_27703 : exactInterval 15 27703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27703 : oddCount 27703 15 = 9 ∧ acceleratedOrbit 15 27703 = 16642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27703) = 3 ^ 9 * m + 16642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27703.1, data_15_27703.2]

/-- Complete interval computation for depth 15, residue 27704. -/
theorem bounds_15_27704 : exactInterval 15 27704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27704 : oddCount 27704 15 = 5 ∧ acceleratedOrbit 15 27704 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27704) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27704.1, data_15_27704.2]

/-- Complete interval computation for depth 15, residue 27705. -/
theorem bounds_15_27705 : exactInterval 15 27705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27705 : oddCount 27705 15 = 9 ∧ acceleratedOrbit 15 27705 = 16645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27705) = 3 ^ 9 * m + 16645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27705.1, data_15_27705.2]

/-- Complete interval computation for depth 15, residue 27706. -/
theorem bounds_15_27706 : exactInterval 15 27706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27706 : oddCount 27706 15 = 5 ∧ acceleratedOrbit 15 27706 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27706) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27706.1, data_15_27706.2]

/-- Complete interval computation for depth 15, residue 27707. -/
theorem bounds_15_27707 : exactInterval 15 27707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27707 : oddCount 27707 15 = 10 ∧ acceleratedOrbit 15 27707 = 49936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27707) = 3 ^ 10 * m + 49936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27707.1, data_15_27707.2]

/-- Complete interval computation for depth 15, residue 27708. -/
theorem bounds_15_27708 : exactInterval 15 27708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27708 : oddCount 27708 15 = 5 ∧ acceleratedOrbit 15 27708 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27708) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27708.1, data_15_27708.2]

/-- Complete interval computation for depth 15, residue 27709. -/
theorem bounds_15_27709 : exactInterval 15 27709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27709 : oddCount 27709 15 = 5 ∧ acceleratedOrbit 15 27709 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27709) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27709.1, data_15_27709.2]

/-- Complete interval computation for depth 15, residue 27710. -/
theorem bounds_15_27710 : exactInterval 15 27710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27710 : oddCount 27710 15 = 10 ∧ acceleratedOrbit 15 27710 = 49940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27710) = 3 ^ 10 * m + 49940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27710.1, data_15_27710.2]

/-- Complete interval computation for depth 15, residue 27711. -/
theorem bounds_15_27711 : exactInterval 15 27711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27711 : oddCount 27711 15 = 10 ∧ acceleratedOrbit 15 27711 = 49940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27711) = 3 ^ 10 * m + 49940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27711.1, data_15_27711.2]

/-- Complete interval computation for depth 15, residue 27712. -/
theorem bounds_15_27712 : exactInterval 15 27712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27712 : oddCount 27712 15 = 3 ∧ acceleratedOrbit 15 27712 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27712) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27712.1, data_15_27712.2]

/-- Complete interval computation for depth 15, residue 27713. -/
theorem bounds_15_27713 : exactInterval 15 27713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27713 : oddCount 27713 15 = 8 ∧ acceleratedOrbit 15 27713 = 5552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27713) = 3 ^ 8 * m + 5552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27713.1, data_15_27713.2]

/-- Complete interval computation for depth 15, residue 27714. -/
theorem bounds_15_27714 : exactInterval 15 27714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27714 : oddCount 27714 15 = 8 ∧ acceleratedOrbit 15 27714 = 5552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27714) = 3 ^ 8 * m + 5552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27714.1, data_15_27714.2]

/-- Complete interval computation for depth 15, residue 27715. -/
theorem bounds_15_27715 : exactInterval 15 27715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27715 : oddCount 27715 15 = 8 ∧ acceleratedOrbit 15 27715 = 5552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27715) = 3 ^ 8 * m + 5552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27715.1, data_15_27715.2]

/-- Complete interval computation for depth 15, residue 27716. -/
theorem bounds_15_27716 : exactInterval 15 27716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27716 : oddCount 27716 15 = 7 ∧ acceleratedOrbit 15 27716 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27716) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27716.1, data_15_27716.2]

/-- Complete interval computation for depth 15, residue 27717. -/
theorem bounds_15_27717 : exactInterval 15 27717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27717 : oddCount 27717 15 = 7 ∧ acceleratedOrbit 15 27717 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27717) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27717.1, data_15_27717.2]

/-- Complete interval computation for depth 15, residue 27718. -/
theorem bounds_15_27718 : exactInterval 15 27718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27718 : oddCount 27718 15 = 7 ∧ acceleratedOrbit 15 27718 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27718) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27718.1, data_15_27718.2]

/-- Complete interval computation for depth 15, residue 27719. -/
theorem bounds_15_27719 : exactInterval 15 27719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27719 : oddCount 27719 15 = 9 ∧ acceleratedOrbit 15 27719 = 16652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27719) = 3 ^ 9 * m + 16652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27719.1, data_15_27719.2]

/-- Complete interval computation for depth 15, residue 27720. -/
theorem bounds_15_27720 : exactInterval 15 27720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27720 : oddCount 27720 15 = 6 ∧ acceleratedOrbit 15 27720 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27720) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27720.1, data_15_27720.2]

end Collatz.Research.PassageAtlas.Batch0846
