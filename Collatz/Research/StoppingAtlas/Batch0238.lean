import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0238

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 568. -/
theorem bounds_12_568 : exactInterval 12 568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_568 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 568) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_568 : oddCount 568 12 = 6 ∧ acceleratedOrbit 12 568 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_568 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 568) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_568.1, data_12_568.2]

/-- Complete interval computation for depth 12, residue 569. -/
theorem bounds_12_569 : exactInterval 12 569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_569 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 569) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_569 : oddCount 569 12 = 8 ∧ acceleratedOrbit 12 569 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_569 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 569) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_569.1, data_12_569.2]

/-- Complete interval computation for depth 12, residue 570. -/
theorem bounds_12_570 : exactInterval 12 570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_570 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 570) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_570 : oddCount 570 12 = 6 ∧ acceleratedOrbit 12 570 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_570 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 570) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_570.1, data_12_570.2]

/-- Complete interval computation for depth 12, residue 571. -/
theorem bounds_12_571 : exactInterval 12 571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_571 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 571) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_571 : oddCount 571 12 = 5 ∧ acceleratedOrbit 12 571 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_571 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 571) = 3 ^ 5 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_571.1, data_12_571.2]

/-- Complete interval computation for depth 12, residue 572. -/
theorem bounds_12_572 : exactInterval 12 572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_572 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 572) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_572 : oddCount 572 12 = 6 ∧ acceleratedOrbit 12 572 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_572 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 572) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_572.1, data_12_572.2]

/-- Complete interval computation for depth 12, residue 573. -/
theorem bounds_12_573 : exactInterval 12 573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_573 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 573) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_573 : oddCount 573 12 = 6 ∧ acceleratedOrbit 12 573 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_573 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 573) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_573.1, data_12_573.2]

/-- Complete interval computation for depth 12, residue 574. -/
theorem bounds_12_574 : exactInterval 12 574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_574 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 574) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_574 : oddCount 574 12 = 7 ∧ acceleratedOrbit 12 574 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_574 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 574) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_574.1, data_12_574.2]

/-- Complete interval computation for depth 12, residue 575. -/
theorem bounds_12_575 : exactInterval 12 575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_575 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 575) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_575 : oddCount 575 12 = 7 ∧ acceleratedOrbit 12 575 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_575 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 575) = 3 ^ 7 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_575.1, data_12_575.2]

/-- Complete interval computation for depth 12, residue 576. -/
theorem bounds_12_576 : exactInterval 12 576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_576 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 576) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_576 : oddCount 576 12 = 4 ∧ acceleratedOrbit 12 576 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_576 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 576) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_576.1, data_12_576.2]

/-- Complete interval computation for depth 12, residue 577. -/
theorem bounds_12_577 : exactInterval 12 577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_577 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 577) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_577 : oddCount 577 12 = 5 ∧ acceleratedOrbit 12 577 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_577 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 577) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_577.1, data_12_577.2]

/-- Complete interval computation for depth 12, residue 578. -/
theorem bounds_12_578 : exactInterval 12 578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_578 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 578) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_578 : oddCount 578 12 = 5 ∧ acceleratedOrbit 12 578 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_578 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 578) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_578.1, data_12_578.2]

/-- Complete interval computation for depth 12, residue 579. -/
theorem bounds_12_579 : exactInterval 12 579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_579 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 579) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_579 : oddCount 579 12 = 5 ∧ acceleratedOrbit 12 579 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_579 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 579) = 3 ^ 5 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_579.1, data_12_579.2]

/-- Complete interval computation for depth 12, residue 580. -/
theorem bounds_12_580 : exactInterval 12 580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_580 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 580) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_580 : oddCount 580 12 = 6 ∧ acceleratedOrbit 12 580 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_580 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 580) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_580.1, data_12_580.2]

/-- Complete interval computation for depth 12, residue 581. -/
theorem bounds_12_581 : exactInterval 12 581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_581 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 581) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_581 : oddCount 581 12 = 6 ∧ acceleratedOrbit 12 581 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_581 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 581) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_581.1, data_12_581.2]

/-- Complete interval computation for depth 12, residue 582. -/
theorem bounds_12_582 : exactInterval 12 582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_582 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 582) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_582 : oddCount 582 12 = 6 ∧ acceleratedOrbit 12 582 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_582 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 582) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_582.1, data_12_582.2]

end Collatz.Research.StoppingAtlas.Batch0238
