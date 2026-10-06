import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0960

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7562. -/
theorem bounds_13_7562 : exactInterval 13 7562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7562 : oddCount 7562 13 = 3 ∧ acceleratedOrbit 13 7562 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7562) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7562.1, data_13_7562.2]

/-- Complete interval computation for depth 13, residue 7563. -/
theorem bounds_13_7563 : exactInterval 13 7563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7563 : oddCount 7563 13 = 7 ∧ acceleratedOrbit 13 7563 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7563) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7563.1, data_13_7563.2]

/-- Complete interval computation for depth 13, residue 7564. -/
theorem bounds_13_7564 : exactInterval 13 7564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7564 : oddCount 7564 13 = 3 ∧ acceleratedOrbit 13 7564 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7564) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7564.1, data_13_7564.2]

/-- Complete interval computation for depth 13, residue 7565. -/
theorem bounds_13_7565 : exactInterval 13 7565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7565 : oddCount 7565 13 = 3 ∧ acceleratedOrbit 13 7565 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7565) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7565.1, data_13_7565.2]

/-- Complete interval computation for depth 13, residue 7566. -/
theorem bounds_13_7566 : exactInterval 13 7566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7566 : oddCount 7566 13 = 6 ∧ acceleratedOrbit 13 7566 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7566) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7566.1, data_13_7566.2]

/-- Complete interval computation for depth 13, residue 7567. -/
theorem bounds_13_7567 : exactInterval 13 7567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7567 : oddCount 7567 13 = 6 ∧ acceleratedOrbit 13 7567 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7567) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7567.1, data_13_7567.2]

/-- Complete interval computation for depth 13, residue 7568. -/
theorem bounds_13_7568 : exactInterval 13 7568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7568 : oddCount 7568 13 = 3 ∧ acceleratedOrbit 13 7568 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7568) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7568.1, data_13_7568.2]

/-- Complete interval computation for depth 13, residue 7569. -/
theorem bounds_13_7569 : exactInterval 13 7569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7569 : oddCount 7569 13 = 7 ∧ acceleratedOrbit 13 7569 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7569) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7569.1, data_13_7569.2]

/-- Complete interval computation for depth 13, residue 7570. -/
theorem bounds_13_7570 : exactInterval 13 7570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7570 : oddCount 7570 13 = 7 ∧ acceleratedOrbit 13 7570 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7570) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7570.1, data_13_7570.2]

/-- Complete interval computation for depth 13, residue 7571. -/
theorem bounds_13_7571 : exactInterval 13 7571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7571 : oddCount 7571 13 = 7 ∧ acceleratedOrbit 13 7571 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7571) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7571.1, data_13_7571.2]

/-- Complete interval computation for depth 13, residue 7572. -/
theorem bounds_13_7572 : exactInterval 13 7572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7572 : oddCount 7572 13 = 3 ∧ acceleratedOrbit 13 7572 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7572) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7572.1, data_13_7572.2]

/-- Complete interval computation for depth 13, residue 7573. -/
theorem bounds_13_7573 : exactInterval 13 7573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7573 : oddCount 7573 13 = 3 ∧ acceleratedOrbit 13 7573 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7573) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7573.1, data_13_7573.2]

/-- Complete interval computation for depth 13, residue 7574. -/
theorem bounds_13_7574 : exactInterval 13 7574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7574 : oddCount 7574 13 = 8 ∧ acceleratedOrbit 13 7574 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7574) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7574.1, data_13_7574.2]

/-- Complete interval computation for depth 13, residue 7575. -/
theorem bounds_13_7575 : exactInterval 13 7575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7575 : oddCount 7575 13 = 8 ∧ acceleratedOrbit 13 7575 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7575) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7575.1, data_13_7575.2]

/-- Complete interval computation for depth 13, residue 7576. -/
theorem bounds_13_7576 : exactInterval 13 7576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7576 : oddCount 7576 13 = 3 ∧ acceleratedOrbit 13 7576 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7576) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7576.1, data_13_7576.2]

end Collatz.Research.StoppingAtlas.Batch0960
