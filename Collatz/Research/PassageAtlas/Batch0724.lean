import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0724

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23691. -/
theorem bounds_15_23691 : exactInterval 15 23691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23691 : oddCount 23691 15 = 8 ∧ acceleratedOrbit 15 23691 = 4745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23691) = 3 ^ 8 * m + 4745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23691.1, data_15_23691.2]

/-- Complete interval computation for depth 15, residue 23692. -/
theorem bounds_15_23692 : exactInterval 15 23692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23692 : oddCount 23692 15 = 5 ∧ acceleratedOrbit 15 23692 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23692) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23692.1, data_15_23692.2]

/-- Complete interval computation for depth 15, residue 23693. -/
theorem bounds_15_23693 : exactInterval 15 23693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23693 : oddCount 23693 15 = 5 ∧ acceleratedOrbit 15 23693 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23693) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23693.1, data_15_23693.2]

/-- Complete interval computation for depth 15, residue 23694. -/
theorem bounds_15_23694 : exactInterval 15 23694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23694 : oddCount 23694 15 = 8 ∧ acceleratedOrbit 15 23694 = 4745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23694) = 3 ^ 8 * m + 4745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23694.1, data_15_23694.2]

/-- Complete interval computation for depth 15, residue 23695. -/
theorem bounds_15_23695 : exactInterval 15 23695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23695 : oddCount 23695 15 = 8 ∧ acceleratedOrbit 15 23695 = 4745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23695) = 3 ^ 8 * m + 4745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23695.1, data_15_23695.2]

/-- Complete interval computation for depth 15, residue 23696. -/
theorem bounds_15_23696 : exactInterval 15 23696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23696 : oddCount 23696 15 = 5 ∧ acceleratedOrbit 15 23696 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23696) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23696.1, data_15_23696.2]

/-- Complete interval computation for depth 15, residue 23697. -/
theorem bounds_15_23697 : exactInterval 15 23697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23697 : oddCount 23697 15 = 7 ∧ acceleratedOrbit 15 23697 = 1582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23697) = 3 ^ 7 * m + 1582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23697.1, data_15_23697.2]

/-- Complete interval computation for depth 15, residue 23698. -/
theorem bounds_15_23698 : exactInterval 15 23698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23698 : oddCount 23698 15 = 7 ∧ acceleratedOrbit 15 23698 = 1582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23698) = 3 ^ 7 * m + 1582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23698.1, data_15_23698.2]

/-- Complete interval computation for depth 15, residue 23699. -/
theorem bounds_15_23699 : exactInterval 15 23699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23699 : oddCount 23699 15 = 7 ∧ acceleratedOrbit 15 23699 = 1582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23699) = 3 ^ 7 * m + 1582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23699.1, data_15_23699.2]

/-- Complete interval computation for depth 15, residue 23700. -/
theorem bounds_15_23700 : exactInterval 15 23700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23700 : oddCount 23700 15 = 5 ∧ acceleratedOrbit 15 23700 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23700) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23700.1, data_15_23700.2]

/-- Complete interval computation for depth 15, residue 23701. -/
theorem bounds_15_23701 : exactInterval 15 23701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23701 : oddCount 23701 15 = 5 ∧ acceleratedOrbit 15 23701 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23701) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23701.1, data_15_23701.2]

/-- Complete interval computation for depth 15, residue 23702. -/
theorem bounds_15_23702 : exactInterval 15 23702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23702 : oddCount 23702 15 = 5 ∧ acceleratedOrbit 15 23702 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23702) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23702.1, data_15_23702.2]

/-- Complete interval computation for depth 15, residue 23703. -/
theorem bounds_15_23703 : exactInterval 15 23703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23703 : oddCount 23703 15 = 5 ∧ acceleratedOrbit 15 23703 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23703) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23703.1, data_15_23703.2]

/-- Complete interval computation for depth 15, residue 23704. -/
theorem bounds_15_23704 : exactInterval 15 23704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23704 : oddCount 23704 15 = 5 ∧ acceleratedOrbit 15 23704 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23704) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23704.1, data_15_23704.2]

/-- Complete interval computation for depth 15, residue 23705. -/
theorem bounds_15_23705 : exactInterval 15 23705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23705 : oddCount 23705 15 = 7 ∧ acceleratedOrbit 15 23705 = 1583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23705) = 3 ^ 7 * m + 1583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23705.1, data_15_23705.2]

/-- Complete interval computation for depth 15, residue 23706. -/
theorem bounds_15_23706 : exactInterval 15 23706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23706 : oddCount 23706 15 = 5 ∧ acceleratedOrbit 15 23706 = 176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23706) = 3 ^ 5 * m + 176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23706.1, data_15_23706.2]

/-- Complete interval computation for depth 15, residue 23707. -/
theorem bounds_15_23707 : exactInterval 15 23707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23707 : oddCount 23707 15 = 10 ∧ acceleratedOrbit 15 23707 = 42724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23707) = 3 ^ 10 * m + 42724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23707.1, data_15_23707.2]

/-- Complete interval computation for depth 15, residue 23708. -/
theorem bounds_15_23708 : exactInterval 15 23708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23708 : oddCount 23708 15 = 9 ∧ acceleratedOrbit 15 23708 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23708) = 3 ^ 9 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23708.1, data_15_23708.2]

/-- Complete interval computation for depth 15, residue 23709. -/
theorem bounds_15_23709 : exactInterval 15 23709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23709 : oddCount 23709 15 = 9 ∧ acceleratedOrbit 15 23709 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23709) = 3 ^ 9 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23709.1, data_15_23709.2]

/-- Complete interval computation for depth 15, residue 23710. -/
theorem bounds_15_23710 : exactInterval 15 23710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23710 : oddCount 23710 15 = 9 ∧ acceleratedOrbit 15 23710 = 14246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23710) = 3 ^ 9 * m + 14246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23710.1, data_15_23710.2]

/-- Complete interval computation for depth 15, residue 23711. -/
theorem bounds_15_23711 : exactInterval 15 23711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23711 : oddCount 23711 15 = 10 ∧ acceleratedOrbit 15 23711 = 42730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23711) = 3 ^ 10 * m + 42730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23711.1, data_15_23711.2]

/-- Complete interval computation for depth 15, residue 23712. -/
theorem bounds_15_23712 : exactInterval 15 23712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23712 : oddCount 23712 15 = 4 ∧ acceleratedOrbit 15 23712 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23712) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23712.1, data_15_23712.2]

/-- Complete interval computation for depth 15, residue 23713. -/
theorem bounds_15_23713 : exactInterval 15 23713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23713 : oddCount 23713 15 = 11 ∧ acceleratedOrbit 15 23713 = 128213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23713) = 3 ^ 11 * m + 128213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23713.1, data_15_23713.2]

/-- Complete interval computation for depth 15, residue 23714. -/
theorem bounds_15_23714 : exactInterval 15 23714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23714 : oddCount 23714 15 = 8 ∧ acceleratedOrbit 15 23714 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23714) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23714.1, data_15_23714.2]

/-- Complete interval computation for depth 15, residue 23715. -/
theorem bounds_15_23715 : exactInterval 15 23715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23715 : oddCount 23715 15 = 8 ∧ acceleratedOrbit 15 23715 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23715) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23715.1, data_15_23715.2]

/-- Complete interval computation for depth 15, residue 23716. -/
theorem bounds_15_23716 : exactInterval 15 23716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23716 : oddCount 23716 15 = 8 ∧ acceleratedOrbit 15 23716 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23716) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23716.1, data_15_23716.2]

/-- Complete interval computation for depth 15, residue 23717. -/
theorem bounds_15_23717 : exactInterval 15 23717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23717 : oddCount 23717 15 = 8 ∧ acceleratedOrbit 15 23717 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23717) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23717.1, data_15_23717.2]

/-- Complete interval computation for depth 15, residue 23718. -/
theorem bounds_15_23718 : exactInterval 15 23718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23718 : oddCount 23718 15 = 8 ∧ acceleratedOrbit 15 23718 = 4751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23718) = 3 ^ 8 * m + 4751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23718.1, data_15_23718.2]

/-- Complete interval computation for depth 15, residue 23719. -/
theorem bounds_15_23719 : exactInterval 15 23719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23719 : oddCount 23719 15 = 11 ∧ acceleratedOrbit 15 23719 = 128236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23719) = 3 ^ 11 * m + 128236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23719.1, data_15_23719.2]

/-- Complete interval computation for depth 15, residue 23720. -/
theorem bounds_15_23720 : exactInterval 15 23720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23720 : oddCount 23720 15 = 4 ∧ acceleratedOrbit 15 23720 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23720) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23720.1, data_15_23720.2]

/-- Complete interval computation for depth 15, residue 23721. -/
theorem bounds_15_23721 : exactInterval 15 23721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23721 : oddCount 23721 15 = 11 ∧ acceleratedOrbit 15 23721 = 128249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23721) = 3 ^ 11 * m + 128249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23721.1, data_15_23721.2]

/-- Complete interval computation for depth 15, residue 23722. -/
theorem bounds_15_23722 : exactInterval 15 23722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23722 : oddCount 23722 15 = 4 ∧ acceleratedOrbit 15 23722 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23722) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23722.1, data_15_23722.2]

/-- Complete interval computation for depth 15, residue 23723. -/
theorem bounds_15_23723 : exactInterval 15 23723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23723 : oddCount 23723 15 = 9 ∧ acceleratedOrbit 15 23723 = 14255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23723) = 3 ^ 9 * m + 14255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23723.1, data_15_23723.2]

end Collatz.Research.PassageAtlas.Batch0724
