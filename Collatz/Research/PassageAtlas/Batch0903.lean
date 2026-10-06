import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0903

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29556. -/
theorem bounds_15_29556 : exactInterval 15 29556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29556 : oddCount 29556 15 = 6 ∧ acceleratedOrbit 15 29556 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29556) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29556.1, data_15_29556.2]

/-- Complete interval computation for depth 15, residue 29557. -/
theorem bounds_15_29557 : exactInterval 15 29557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29557 : oddCount 29557 15 = 6 ∧ acceleratedOrbit 15 29557 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29557) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29557.1, data_15_29557.2]

/-- Complete interval computation for depth 15, residue 29558. -/
theorem bounds_15_29558 : exactInterval 15 29558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29558 : oddCount 29558 15 = 9 ∧ acceleratedOrbit 15 29558 = 17759 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29558) = 3 ^ 9 * m + 17759 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29558.1, data_15_29558.2]

/-- Complete interval computation for depth 15, residue 29559. -/
theorem bounds_15_29559 : exactInterval 15 29559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29559 : oddCount 29559 15 = 9 ∧ acceleratedOrbit 15 29559 = 17759 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29559) = 3 ^ 9 * m + 17759 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29559.1, data_15_29559.2]

/-- Complete interval computation for depth 15, residue 29560. -/
theorem bounds_15_29560 : exactInterval 15 29560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29560 : oddCount 29560 15 = 8 ∧ acceleratedOrbit 15 29560 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29560) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29560.1, data_15_29560.2]

/-- Complete interval computation for depth 15, residue 29561. -/
theorem bounds_15_29561 : exactInterval 15 29561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29561 : oddCount 29561 15 = 9 ∧ acceleratedOrbit 15 29561 = 17758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29561) = 3 ^ 9 * m + 17758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29561.1, data_15_29561.2]

/-- Complete interval computation for depth 15, residue 29562. -/
theorem bounds_15_29562 : exactInterval 15 29562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29562 : oddCount 29562 15 = 8 ∧ acceleratedOrbit 15 29562 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29562) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29562.1, data_15_29562.2]

/-- Complete interval computation for depth 15, residue 29563. -/
theorem bounds_15_29563 : exactInterval 15 29563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29563 : oddCount 29563 15 = 11 ∧ acceleratedOrbit 15 29563 = 159833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29563) = 3 ^ 11 * m + 159833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29563.1, data_15_29563.2]

/-- Complete interval computation for depth 15, residue 29564. -/
theorem bounds_15_29564 : exactInterval 15 29564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29564 : oddCount 29564 15 = 8 ∧ acceleratedOrbit 15 29564 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29564) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29564.1, data_15_29564.2]

/-- Complete interval computation for depth 15, residue 29565. -/
theorem bounds_15_29565 : exactInterval 15 29565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29565 : oddCount 29565 15 = 8 ∧ acceleratedOrbit 15 29565 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29565) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29565.1, data_15_29565.2]

/-- Complete interval computation for depth 15, residue 29566. -/
theorem bounds_15_29566 : exactInterval 15 29566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29566 : oddCount 29566 15 = 12 ∧ acceleratedOrbit 15 29566 = 479546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29566) = 3 ^ 12 * m + 479546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29566.1, data_15_29566.2]

/-- Complete interval computation for depth 15, residue 29567. -/
theorem bounds_15_29567 : exactInterval 15 29567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29567 : oddCount 29567 15 = 12 ∧ acceleratedOrbit 15 29567 = 479546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29567) = 3 ^ 12 * m + 479546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29567.1, data_15_29567.2]

/-- Complete interval computation for depth 15, residue 29568. -/
theorem bounds_15_29568 : exactInterval 15 29568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29568 : oddCount 29568 15 = 6 ∧ acceleratedOrbit 15 29568 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29568) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29568.1, data_15_29568.2]

/-- Complete interval computation for depth 15, residue 29569. -/
theorem bounds_15_29569 : exactInterval 15 29569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29569 : oddCount 29569 15 = 9 ∧ acceleratedOrbit 15 29569 = 17765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29569) = 3 ^ 9 * m + 17765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29569.1, data_15_29569.2]

/-- Complete interval computation for depth 15, residue 29570. -/
theorem bounds_15_29570 : exactInterval 15 29570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29570 : oddCount 29570 15 = 8 ∧ acceleratedOrbit 15 29570 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29570) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29570.1, data_15_29570.2]

/-- Complete interval computation for depth 15, residue 29571. -/
theorem bounds_15_29571 : exactInterval 15 29571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29571 : oddCount 29571 15 = 8 ∧ acceleratedOrbit 15 29571 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29571) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29571.1, data_15_29571.2]

/-- Complete interval computation for depth 15, residue 29572. -/
theorem bounds_15_29572 : exactInterval 15 29572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29572 : oddCount 29572 15 = 8 ∧ acceleratedOrbit 15 29572 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29572) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29572.1, data_15_29572.2]

/-- Complete interval computation for depth 15, residue 29573. -/
theorem bounds_15_29573 : exactInterval 15 29573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29573 : oddCount 29573 15 = 8 ∧ acceleratedOrbit 15 29573 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29573) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29573.1, data_15_29573.2]

/-- Complete interval computation for depth 15, residue 29574. -/
theorem bounds_15_29574 : exactInterval 15 29574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29574 : oddCount 29574 15 = 8 ∧ acceleratedOrbit 15 29574 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29574) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29574.1, data_15_29574.2]

/-- Complete interval computation for depth 15, residue 29575. -/
theorem bounds_15_29575 : exactInterval 15 29575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29575 : oddCount 29575 15 = 8 ∧ acceleratedOrbit 15 29575 = 5923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29575) = 3 ^ 8 * m + 5923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29575.1, data_15_29575.2]

/-- Complete interval computation for depth 15, residue 29576. -/
theorem bounds_15_29576 : exactInterval 15 29576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29576 : oddCount 29576 15 = 4 ∧ acceleratedOrbit 15 29576 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29576) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29576.1, data_15_29576.2]

/-- Complete interval computation for depth 15, residue 29577. -/
theorem bounds_15_29577 : exactInterval 15 29577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29577 : oddCount 29577 15 = 9 ∧ acceleratedOrbit 15 29577 = 17768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29577) = 3 ^ 9 * m + 17768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29577.1, data_15_29577.2]

/-- Complete interval computation for depth 15, residue 29578. -/
theorem bounds_15_29578 : exactInterval 15 29578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29578 : oddCount 29578 15 = 4 ∧ acceleratedOrbit 15 29578 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29578) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29578.1, data_15_29578.2]

/-- Complete interval computation for depth 15, residue 29579. -/
theorem bounds_15_29579 : exactInterval 15 29579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29579 : oddCount 29579 15 = 10 ∧ acceleratedOrbit 15 29579 = 53308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29579) = 3 ^ 10 * m + 53308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29579.1, data_15_29579.2]

/-- Complete interval computation for depth 15, residue 29580. -/
theorem bounds_15_29580 : exactInterval 15 29580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29580 : oddCount 29580 15 = 4 ∧ acceleratedOrbit 15 29580 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29580) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29580.1, data_15_29580.2]

/-- Complete interval computation for depth 15, residue 29581. -/
theorem bounds_15_29581 : exactInterval 15 29581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29581 : oddCount 29581 15 = 4 ∧ acceleratedOrbit 15 29581 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29581) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29581.1, data_15_29581.2]

/-- Complete interval computation for depth 15, residue 29582. -/
theorem bounds_15_29582 : exactInterval 15 29582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29582 : oddCount 29582 15 = 8 ∧ acceleratedOrbit 15 29582 = 5924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29582) = 3 ^ 8 * m + 5924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29582.1, data_15_29582.2]

/-- Complete interval computation for depth 15, residue 29583. -/
theorem bounds_15_29583 : exactInterval 15 29583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29583 : oddCount 29583 15 = 8 ∧ acceleratedOrbit 15 29583 = 5924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29583) = 3 ^ 8 * m + 5924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29583.1, data_15_29583.2]

/-- Complete interval computation for depth 15, residue 29584. -/
theorem bounds_15_29584 : exactInterval 15 29584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29584 : oddCount 29584 15 = 6 ∧ acceleratedOrbit 15 29584 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29584) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29584.1, data_15_29584.2]

/-- Complete interval computation for depth 15, residue 29585. -/
theorem bounds_15_29585 : exactInterval 15 29585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29585 : oddCount 29585 15 = 8 ∧ acceleratedOrbit 15 29585 = 5926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29585) = 3 ^ 8 * m + 5926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29585.1, data_15_29585.2]

/-- Complete interval computation for depth 15, residue 29586. -/
theorem bounds_15_29586 : exactInterval 15 29586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29586 : oddCount 29586 15 = 8 ∧ acceleratedOrbit 15 29586 = 5926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29586) = 3 ^ 8 * m + 5926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29586.1, data_15_29586.2]

/-- Complete interval computation for depth 15, residue 29587. -/
theorem bounds_15_29587 : exactInterval 15 29587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29587 : oddCount 29587 15 = 8 ∧ acceleratedOrbit 15 29587 = 5926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29587) = 3 ^ 8 * m + 5926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29587.1, data_15_29587.2]

/-- Complete interval computation for depth 15, residue 29588. -/
theorem bounds_15_29588 : exactInterval 15 29588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29588 : oddCount 29588 15 = 6 ∧ acceleratedOrbit 15 29588 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29588) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29588.1, data_15_29588.2]

end Collatz.Research.PassageAtlas.Batch0903
