import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0895

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6563. -/
theorem bounds_13_6563 : exactInterval 13 6563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6563 : oddCount 6563 13 = 8 ∧ acceleratedOrbit 13 6563 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6563) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6563.1, data_13_6563.2]

/-- Complete interval computation for depth 13, residue 6564. -/
theorem bounds_13_6564 : exactInterval 13 6564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6564 : oddCount 6564 13 = 8 ∧ acceleratedOrbit 13 6564 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6564) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6564.1, data_13_6564.2]

/-- Complete interval computation for depth 13, residue 6565. -/
theorem bounds_13_6565 : exactInterval 13 6565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6565 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6565) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6565 : oddCount 6565 13 = 8 ∧ acceleratedOrbit 13 6565 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6565 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6565) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6565.1, data_13_6565.2]

/-- Complete interval computation for depth 13, residue 6566. -/
theorem bounds_13_6566 : exactInterval 13 6566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6566 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6566) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6566 : oddCount 6566 13 = 8 ∧ acceleratedOrbit 13 6566 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6566 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6566) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6566.1, data_13_6566.2]

/-- Complete interval computation for depth 13, residue 6567. -/
theorem bounds_13_6567 : exactInterval 13 6567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6567 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6567) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6567 : oddCount 6567 13 = 7 ∧ acceleratedOrbit 13 6567 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6567 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6567) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6567.1, data_13_6567.2]

/-- Complete interval computation for depth 13, residue 6568. -/
theorem bounds_13_6568 : exactInterval 13 6568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6568 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6568) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6568 : oddCount 6568 13 = 3 ∧ acceleratedOrbit 13 6568 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6568 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6568) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6568.1, data_13_6568.2]

/-- Complete interval computation for depth 13, residue 6569. -/
theorem bounds_13_6569 : exactInterval 13 6569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6569 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6569) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6569 : oddCount 6569 13 = 9 ∧ acceleratedOrbit 13 6569 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6569 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6569) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6569.1, data_13_6569.2]

/-- Complete interval computation for depth 13, residue 6570. -/
theorem bounds_13_6570 : exactInterval 13 6570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6570 : oddCount 6570 13 = 3 ∧ acceleratedOrbit 13 6570 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6570) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6570.1, data_13_6570.2]

/-- Complete interval computation for depth 13, residue 6571. -/
theorem bounds_13_6571 : exactInterval 13 6571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6571 : oddCount 6571 13 = 10 ∧ acceleratedOrbit 13 6571 = 47384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6571) = 3 ^ 10 * m + 47384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6571.1, data_13_6571.2]

/-- Complete interval computation for depth 13, residue 6572. -/
theorem bounds_13_6572 : exactInterval 13 6572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6572 : oddCount 6572 13 = 7 ∧ acceleratedOrbit 13 6572 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6572) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6572.1, data_13_6572.2]

/-- Complete interval computation for depth 13, residue 6573. -/
theorem bounds_13_6573 : exactInterval 13 6573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6573 : oddCount 6573 13 = 7 ∧ acceleratedOrbit 13 6573 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6573) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6573.1, data_13_6573.2]

/-- Complete interval computation for depth 13, residue 6574. -/
theorem bounds_13_6574 : exactInterval 13 6574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6574 : oddCount 6574 13 = 7 ∧ acceleratedOrbit 13 6574 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6574) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6574.1, data_13_6574.2]

/-- Complete interval computation for depth 13, residue 6575. -/
theorem bounds_13_6575 : exactInterval 13 6575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6575 : oddCount 6575 13 = 7 ∧ acceleratedOrbit 13 6575 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6575) = 3 ^ 7 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6575.1, data_13_6575.2]

/-- Complete interval computation for depth 13, residue 6576. -/
theorem bounds_13_6576 : exactInterval 13 6576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6576 : oddCount 6576 13 = 6 ∧ acceleratedOrbit 13 6576 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6576) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6576.1, data_13_6576.2]

/-- Complete interval computation for depth 13, residue 6577. -/
theorem bounds_13_6577 : exactInterval 13 6577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6577 : oddCount 6577 13 = 6 ∧ acceleratedOrbit 13 6577 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6577) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6577.1, data_13_6577.2]

/-- Complete interval computation for depth 13, residue 6578. -/
theorem bounds_13_6578 : exactInterval 13 6578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6578 : oddCount 6578 13 = 6 ∧ acceleratedOrbit 13 6578 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6578) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6578.1, data_13_6578.2]

end Collatz.Research.StoppingAtlas.Batch0895
