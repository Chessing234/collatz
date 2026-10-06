import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0880

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28803. -/
theorem bounds_15_28803 : exactInterval 15 28803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28803 : oddCount 28803 15 = 8 ∧ acceleratedOrbit 15 28803 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28803) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28803.1, data_15_28803.2]

/-- Complete interval computation for depth 15, residue 28804. -/
theorem bounds_15_28804 : exactInterval 15 28804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28804 : oddCount 28804 15 = 8 ∧ acceleratedOrbit 15 28804 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28804) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28804.1, data_15_28804.2]

/-- Complete interval computation for depth 15, residue 28805. -/
theorem bounds_15_28805 : exactInterval 15 28805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28805 : oddCount 28805 15 = 8 ∧ acceleratedOrbit 15 28805 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28805) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28805.1, data_15_28805.2]

/-- Complete interval computation for depth 15, residue 28806. -/
theorem bounds_15_28806 : exactInterval 15 28806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28806 : oddCount 28806 15 = 8 ∧ acceleratedOrbit 15 28806 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28806) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28806.1, data_15_28806.2]

/-- Complete interval computation for depth 15, residue 28807. -/
theorem bounds_15_28807 : exactInterval 15 28807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28807 : oddCount 28807 15 = 10 ∧ acceleratedOrbit 15 28807 = 51920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28807) = 3 ^ 10 * m + 51920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28807.1, data_15_28807.2]

/-- Complete interval computation for depth 15, residue 28808. -/
theorem bounds_15_28808 : exactInterval 15 28808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28808 : oddCount 28808 15 = 5 ∧ acceleratedOrbit 15 28808 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28808) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28808.1, data_15_28808.2]

/-- Complete interval computation for depth 15, residue 28809. -/
theorem bounds_15_28809 : exactInterval 15 28809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28809 : oddCount 28809 15 = 11 ∧ acceleratedOrbit 15 28809 = 155756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28809) = 3 ^ 11 * m + 155756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28809.1, data_15_28809.2]

/-- Complete interval computation for depth 15, residue 28810. -/
theorem bounds_15_28810 : exactInterval 15 28810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28810 : oddCount 28810 15 = 5 ∧ acceleratedOrbit 15 28810 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28810) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28810.1, data_15_28810.2]

/-- Complete interval computation for depth 15, residue 28811. -/
theorem bounds_15_28811 : exactInterval 15 28811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28811 : oddCount 28811 15 = 9 ∧ acceleratedOrbit 15 28811 = 17309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28811) = 3 ^ 9 * m + 17309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28811.1, data_15_28811.2]

/-- Complete interval computation for depth 15, residue 28812. -/
theorem bounds_15_28812 : exactInterval 15 28812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28812 : oddCount 28812 15 = 5 ∧ acceleratedOrbit 15 28812 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28812) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28812.1, data_15_28812.2]

/-- Complete interval computation for depth 15, residue 28813. -/
theorem bounds_15_28813 : exactInterval 15 28813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28813 : oddCount 28813 15 = 5 ∧ acceleratedOrbit 15 28813 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28813) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28813.1, data_15_28813.2]

/-- Complete interval computation for depth 15, residue 28814. -/
theorem bounds_15_28814 : exactInterval 15 28814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28814 : oddCount 28814 15 = 8 ∧ acceleratedOrbit 15 28814 = 5770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28814) = 3 ^ 8 * m + 5770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28814.1, data_15_28814.2]

/-- Complete interval computation for depth 15, residue 28815. -/
theorem bounds_15_28815 : exactInterval 15 28815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28815 : oddCount 28815 15 = 8 ∧ acceleratedOrbit 15 28815 = 5770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28815) = 3 ^ 8 * m + 5770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28815.1, data_15_28815.2]

/-- Complete interval computation for depth 15, residue 28816. -/
theorem bounds_15_28816 : exactInterval 15 28816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28816 : oddCount 28816 15 = 8 ∧ acceleratedOrbit 15 28816 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28816) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28816.1, data_15_28816.2]

/-- Complete interval computation for depth 15, residue 28817. -/
theorem bounds_15_28817 : exactInterval 15 28817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28817 : oddCount 28817 15 = 10 ∧ acceleratedOrbit 15 28817 = 51941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28817) = 3 ^ 10 * m + 51941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28817.1, data_15_28817.2]

/-- Complete interval computation for depth 15, residue 28818. -/
theorem bounds_15_28818 : exactInterval 15 28818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28818 : oddCount 28818 15 = 10 ∧ acceleratedOrbit 15 28818 = 51941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28818) = 3 ^ 10 * m + 51941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28818.1, data_15_28818.2]

/-- Complete interval computation for depth 15, residue 28819. -/
theorem bounds_15_28819 : exactInterval 15 28819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28819 : oddCount 28819 15 = 10 ∧ acceleratedOrbit 15 28819 = 51941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28819) = 3 ^ 10 * m + 51941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28819.1, data_15_28819.2]

/-- Complete interval computation for depth 15, residue 28820. -/
theorem bounds_15_28820 : exactInterval 15 28820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28820 : oddCount 28820 15 = 8 ∧ acceleratedOrbit 15 28820 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28820) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28820.1, data_15_28820.2]

/-- Complete interval computation for depth 15, residue 28821. -/
theorem bounds_15_28821 : exactInterval 15 28821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28821 : oddCount 28821 15 = 8 ∧ acceleratedOrbit 15 28821 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28821) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28821.1, data_15_28821.2]

/-- Complete interval computation for depth 15, residue 28822. -/
theorem bounds_15_28822 : exactInterval 15 28822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28822 : oddCount 28822 15 = 5 ∧ acceleratedOrbit 15 28822 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28822) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28822.1, data_15_28822.2]

/-- Complete interval computation for depth 15, residue 28823. -/
theorem bounds_15_28823 : exactInterval 15 28823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28823 : oddCount 28823 15 = 5 ∧ acceleratedOrbit 15 28823 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28823) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28823.1, data_15_28823.2]

/-- Complete interval computation for depth 15, residue 28824. -/
theorem bounds_15_28824 : exactInterval 15 28824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28824 : oddCount 28824 15 = 8 ∧ acceleratedOrbit 15 28824 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28824) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28824.1, data_15_28824.2]

/-- Complete interval computation for depth 15, residue 28825. -/
theorem bounds_15_28825 : exactInterval 15 28825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28825 : oddCount 28825 15 = 8 ∧ acceleratedOrbit 15 28825 = 5773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28825) = 3 ^ 8 * m + 5773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28825.1, data_15_28825.2]

/-- Complete interval computation for depth 15, residue 28826. -/
theorem bounds_15_28826 : exactInterval 15 28826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28826 : oddCount 28826 15 = 8 ∧ acceleratedOrbit 15 28826 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28826) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28826.1, data_15_28826.2]

/-- Complete interval computation for depth 15, residue 28827. -/
theorem bounds_15_28827 : exactInterval 15 28827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28827 : oddCount 28827 15 = 9 ∧ acceleratedOrbit 15 28827 = 17317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28827) = 3 ^ 9 * m + 17317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28827.1, data_15_28827.2]

/-- Complete interval computation for depth 15, residue 28828. -/
theorem bounds_15_28828 : exactInterval 15 28828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28828 : oddCount 28828 15 = 7 ∧ acceleratedOrbit 15 28828 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28828) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28828.1, data_15_28828.2]

/-- Complete interval computation for depth 15, residue 28829. -/
theorem bounds_15_28829 : exactInterval 15 28829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28829 : oddCount 28829 15 = 7 ∧ acceleratedOrbit 15 28829 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28829) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28829.1, data_15_28829.2]

/-- Complete interval computation for depth 15, residue 28830. -/
theorem bounds_15_28830 : exactInterval 15 28830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28830 : oddCount 28830 15 = 7 ∧ acceleratedOrbit 15 28830 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28830) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28830.1, data_15_28830.2]

/-- Complete interval computation for depth 15, residue 28831. -/
theorem bounds_15_28831 : exactInterval 15 28831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28831 : oddCount 28831 15 = 12 ∧ acceleratedOrbit 15 28831 = 467608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28831) = 3 ^ 12 * m + 467608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28831.1, data_15_28831.2]

/-- Complete interval computation for depth 15, residue 28832. -/
theorem bounds_15_28832 : exactInterval 15 28832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28832 : oddCount 28832 15 = 6 ∧ acceleratedOrbit 15 28832 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28832) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28832.1, data_15_28832.2]

/-- Complete interval computation for depth 15, residue 28833. -/
theorem bounds_15_28833 : exactInterval 15 28833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28833 : oddCount 28833 15 = 10 ∧ acceleratedOrbit 15 28833 = 51965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28833) = 3 ^ 10 * m + 51965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28833.1, data_15_28833.2]

/-- Complete interval computation for depth 15, residue 28834. -/
theorem bounds_15_28834 : exactInterval 15 28834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28834 : oddCount 28834 15 = 8 ∧ acceleratedOrbit 15 28834 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28834) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28834.1, data_15_28834.2]

end Collatz.Research.PassageAtlas.Batch0880
