import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0785

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25690. -/
theorem bounds_15_25690 : exactInterval 15 25690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25690 : oddCount 25690 15 = 6 ∧ acceleratedOrbit 15 25690 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25690) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25690.1, data_15_25690.2]

/-- Complete interval computation for depth 15, residue 25691. -/
theorem bounds_15_25691 : exactInterval 15 25691 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25691) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25691 : oddCount 25691 15 = 9 ∧ acceleratedOrbit 15 25691 = 15433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25691) = 3 ^ 9 * m + 15433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25691.1, data_15_25691.2]

/-- Complete interval computation for depth 15, residue 25692. -/
theorem bounds_15_25692 : exactInterval 15 25692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25692 : oddCount 25692 15 = 6 ∧ acceleratedOrbit 15 25692 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25692) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25692.1, data_15_25692.2]

/-- Complete interval computation for depth 15, residue 25693. -/
theorem bounds_15_25693 : exactInterval 15 25693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25693 : oddCount 25693 15 = 6 ∧ acceleratedOrbit 15 25693 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25693) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25693.1, data_15_25693.2]

/-- Complete interval computation for depth 15, residue 25694. -/
theorem bounds_15_25694 : exactInterval 15 25694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25694 : oddCount 25694 15 = 10 ∧ acceleratedOrbit 15 25694 = 46307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25694) = 3 ^ 10 * m + 46307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25694.1, data_15_25694.2]

/-- Complete interval computation for depth 15, residue 25695. -/
theorem bounds_15_25695 : exactInterval 15 25695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25695 : oddCount 25695 15 = 10 ∧ acceleratedOrbit 15 25695 = 46307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25695) = 3 ^ 10 * m + 46307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25695.1, data_15_25695.2]

/-- Complete interval computation for depth 15, residue 25696. -/
theorem bounds_15_25696 : exactInterval 15 25696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25696 : oddCount 25696 15 = 4 ∧ acceleratedOrbit 15 25696 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25696) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25696.1, data_15_25696.2]

/-- Complete interval computation for depth 15, residue 25697. -/
theorem bounds_15_25697 : exactInterval 15 25697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25697 : oddCount 25697 15 = 8 ∧ acceleratedOrbit 15 25697 = 5147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25697) = 3 ^ 8 * m + 5147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25697.1, data_15_25697.2]

/-- Complete interval computation for depth 15, residue 25698. -/
theorem bounds_15_25698 : exactInterval 15 25698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25698 : oddCount 25698 15 = 6 ∧ acceleratedOrbit 15 25698 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25698) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25698.1, data_15_25698.2]

/-- Complete interval computation for depth 15, residue 25699. -/
theorem bounds_15_25699 : exactInterval 15 25699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25699 : oddCount 25699 15 = 6 ∧ acceleratedOrbit 15 25699 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25699) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25699.1, data_15_25699.2]

/-- Complete interval computation for depth 15, residue 25700. -/
theorem bounds_15_25700 : exactInterval 15 25700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25700 : oddCount 25700 15 = 6 ∧ acceleratedOrbit 15 25700 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25700) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25700.1, data_15_25700.2]

/-- Complete interval computation for depth 15, residue 25701. -/
theorem bounds_15_25701 : exactInterval 15 25701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25701 : oddCount 25701 15 = 6 ∧ acceleratedOrbit 15 25701 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25701) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25701.1, data_15_25701.2]

/-- Complete interval computation for depth 15, residue 25702. -/
theorem bounds_15_25702 : exactInterval 15 25702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25702 : oddCount 25702 15 = 6 ∧ acceleratedOrbit 15 25702 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25702) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25702.1, data_15_25702.2]

/-- Complete interval computation for depth 15, residue 25703. -/
theorem bounds_15_25703 : exactInterval 15 25703 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25703) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25703 : oddCount 25703 15 = 9 ∧ acceleratedOrbit 15 25703 = 15440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25703) = 3 ^ 9 * m + 15440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25703.1, data_15_25703.2]

/-- Complete interval computation for depth 15, residue 25704. -/
theorem bounds_15_25704 : exactInterval 15 25704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25704 : oddCount 25704 15 = 4 ∧ acceleratedOrbit 15 25704 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25704) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25704.1, data_15_25704.2]

/-- Complete interval computation for depth 15, residue 25705. -/
theorem bounds_15_25705 : exactInterval 15 25705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25705 : oddCount 25705 15 = 9 ∧ acceleratedOrbit 15 25705 = 15443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25705) = 3 ^ 9 * m + 15443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25705.1, data_15_25705.2]

/-- Complete interval computation for depth 15, residue 25706. -/
theorem bounds_15_25706 : exactInterval 15 25706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25706 : oddCount 25706 15 = 4 ∧ acceleratedOrbit 15 25706 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25706) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25706.1, data_15_25706.2]

/-- Complete interval computation for depth 15, residue 25707. -/
theorem bounds_15_25707 : exactInterval 15 25707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25707 : oddCount 25707 15 = 10 ∧ acceleratedOrbit 15 25707 = 46331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25707) = 3 ^ 10 * m + 46331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25707.1, data_15_25707.2]

/-- Complete interval computation for depth 15, residue 25708. -/
theorem bounds_15_25708 : exactInterval 15 25708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25708 : oddCount 25708 15 = 9 ∧ acceleratedOrbit 15 25708 = 15446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25708) = 3 ^ 9 * m + 15446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25708.1, data_15_25708.2]

/-- Complete interval computation for depth 15, residue 25709. -/
theorem bounds_15_25709 : exactInterval 15 25709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25709 : oddCount 25709 15 = 9 ∧ acceleratedOrbit 15 25709 = 15446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25709) = 3 ^ 9 * m + 15446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25709.1, data_15_25709.2]

/-- Complete interval computation for depth 15, residue 25710. -/
theorem bounds_15_25710 : exactInterval 15 25710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25710 : oddCount 25710 15 = 9 ∧ acceleratedOrbit 15 25710 = 15446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25710) = 3 ^ 9 * m + 15446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25710.1, data_15_25710.2]

/-- Complete interval computation for depth 15, residue 25711. -/
theorem bounds_15_25711 : exactInterval 15 25711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25711 : oddCount 25711 15 = 9 ∧ acceleratedOrbit 15 25711 = 15445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25711) = 3 ^ 9 * m + 15445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25711.1, data_15_25711.2]

/-- Complete interval computation for depth 15, residue 25712. -/
theorem bounds_15_25712 : exactInterval 15 25712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25712 : oddCount 25712 15 = 7 ∧ acceleratedOrbit 15 25712 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25712) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25712.1, data_15_25712.2]

/-- Complete interval computation for depth 15, residue 25713. -/
theorem bounds_15_25713 : exactInterval 15 25713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25713 : oddCount 25713 15 = 4 ∧ acceleratedOrbit 15 25713 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25713) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25713.1, data_15_25713.2]

/-- Complete interval computation for depth 15, residue 25714. -/
theorem bounds_15_25714 : exactInterval 15 25714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25714 : oddCount 25714 15 = 8 ∧ acceleratedOrbit 15 25714 = 5150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25714) = 3 ^ 8 * m + 5150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25714.1, data_15_25714.2]

/-- Complete interval computation for depth 15, residue 25715. -/
theorem bounds_15_25715 : exactInterval 15 25715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25715 : oddCount 25715 15 = 8 ∧ acceleratedOrbit 15 25715 = 5150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25715) = 3 ^ 8 * m + 5150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25715.1, data_15_25715.2]

/-- Complete interval computation for depth 15, residue 25716. -/
theorem bounds_15_25716 : exactInterval 15 25716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25716 : oddCount 25716 15 = 7 ∧ acceleratedOrbit 15 25716 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25716) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25716.1, data_15_25716.2]

/-- Complete interval computation for depth 15, residue 25717. -/
theorem bounds_15_25717 : exactInterval 15 25717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25717 : oddCount 25717 15 = 7 ∧ acceleratedOrbit 15 25717 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25717) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25717.1, data_15_25717.2]

/-- Complete interval computation for depth 15, residue 25718. -/
theorem bounds_15_25718 : exactInterval 15 25718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25718 : oddCount 25718 15 = 7 ∧ acceleratedOrbit 15 25718 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25718) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25718.1, data_15_25718.2]

/-- Complete interval computation for depth 15, residue 25719. -/
theorem bounds_15_25719 : exactInterval 15 25719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25719 : oddCount 25719 15 = 7 ∧ acceleratedOrbit 15 25719 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25719) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25719.1, data_15_25719.2]

/-- Complete interval computation for depth 15, residue 25720. -/
theorem bounds_15_25720 : exactInterval 15 25720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25720 : oddCount 25720 15 = 7 ∧ acceleratedOrbit 15 25720 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25720) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25720.1, data_15_25720.2]

/-- Complete interval computation for depth 15, residue 25721. -/
theorem bounds_15_25721 : exactInterval 15 25721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25721 : oddCount 25721 15 = 9 ∧ acceleratedOrbit 15 25721 = 15452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25721) = 3 ^ 9 * m + 15452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25721.1, data_15_25721.2]

end Collatz.Research.PassageAtlas.Batch0785
