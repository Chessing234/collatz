import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0038

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 568. -/
theorem bounds_10_568 : exactInterval 10 568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_568 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 568) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_568 : oddCount 568 10 = 5 ∧ acceleratedOrbit 10 568 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_568 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 568) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_568.1, data_10_568.2]

/-- Complete interval computation for depth 10, residue 569. -/
theorem bounds_10_569 : exactInterval 10 569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_569 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 569) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_569 : oddCount 569 10 = 6 ∧ acceleratedOrbit 10 569 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_569 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 569) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_569.1, data_10_569.2]

/-- Complete interval computation for depth 10, residue 570. -/
theorem bounds_10_570 : exactInterval 10 570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_570 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 570) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_570 : oddCount 570 10 = 5 ∧ acceleratedOrbit 10 570 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_570 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 570) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_570.1, data_10_570.2]

/-- Complete interval computation for depth 10, residue 571. -/
theorem bounds_10_571 : exactInterval 10 571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_571 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 571) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_571 : oddCount 571 10 = 5 ∧ acceleratedOrbit 10 571 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_571 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 571) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_571.1, data_10_571.2]

/-- Complete interval computation for depth 10, residue 572. -/
theorem bounds_10_572 : exactInterval 10 572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_572 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 572) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_572 : oddCount 572 10 = 5 ∧ acceleratedOrbit 10 572 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_572 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 572) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_572.1, data_10_572.2]

/-- Complete interval computation for depth 10, residue 573. -/
theorem bounds_10_573 : exactInterval 10 573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_573 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 573) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_573 : oddCount 573 10 = 5 ∧ acceleratedOrbit 10 573 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_573 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 573) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_573.1, data_10_573.2]

/-- Complete interval computation for depth 10, residue 574. -/
theorem bounds_10_574 : exactInterval 10 574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_574 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 574) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_574 : oddCount 574 10 = 6 ∧ acceleratedOrbit 10 574 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_574 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 574) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_574.1, data_10_574.2]

/-- Complete interval computation for depth 10, residue 575. -/
theorem bounds_10_575 : exactInterval 10 575 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_575 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 575) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_575 : oddCount 575 10 = 6 ∧ acceleratedOrbit 10 575 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_575 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 575) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_575.1, data_10_575.2]

/-- Complete interval computation for depth 10, residue 576. -/
theorem bounds_10_576 : exactInterval 10 576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_576 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 576) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_576 : oddCount 576 10 = 3 ∧ acceleratedOrbit 10 576 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_576 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 576) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_576.1, data_10_576.2]

/-- Complete interval computation for depth 10, residue 577. -/
theorem bounds_10_577 : exactInterval 10 577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_577 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 577) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_577 : oddCount 577 10 = 4 ∧ acceleratedOrbit 10 577 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_577 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 577) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_577.1, data_10_577.2]

/-- Complete interval computation for depth 10, residue 578. -/
theorem bounds_10_578 : exactInterval 10 578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_578 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 578) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_578 : oddCount 578 10 = 4 ∧ acceleratedOrbit 10 578 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_578 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 578) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_578.1, data_10_578.2]

/-- Complete interval computation for depth 10, residue 579. -/
theorem bounds_10_579 : exactInterval 10 579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_579 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 579) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_579 : oddCount 579 10 = 4 ∧ acceleratedOrbit 10 579 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_579 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 579) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_579.1, data_10_579.2]

/-- Complete interval computation for depth 10, residue 580. -/
theorem bounds_10_580 : exactInterval 10 580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_580 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 580) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_580 : oddCount 580 10 = 4 ∧ acceleratedOrbit 10 580 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_580 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 580) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_580.1, data_10_580.2]

/-- Complete interval computation for depth 10, residue 581. -/
theorem bounds_10_581 : exactInterval 10 581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_581 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 581) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_581 : oddCount 581 10 = 4 ∧ acceleratedOrbit 10 581 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_581 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 581) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_581.1, data_10_581.2]

/-- Complete interval computation for depth 10, residue 582. -/
theorem bounds_10_582 : exactInterval 10 582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_582 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 582) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_582 : oddCount 582 10 = 4 ∧ acceleratedOrbit 10 582 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_582 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 582) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_582.1, data_10_582.2]

end Collatz.Research.StoppingAtlas.Batch0038
