import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0505

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 573. -/
theorem bounds_13_573 : exactInterval 13 573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_573 : oddCount 573 13 = 7 ∧ acceleratedOrbit 13 573 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 573) = 3 ^ 7 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_573.1, data_13_573.2]

/-- Complete interval computation for depth 13, residue 574. -/
theorem bounds_13_574 : exactInterval 13 574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_574 : oddCount 574 13 = 7 ∧ acceleratedOrbit 13 574 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 574) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_574.1, data_13_574.2]

/-- Complete interval computation for depth 13, residue 575. -/
theorem bounds_13_575 : exactInterval 13 575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_575 : oddCount 575 13 = 7 ∧ acceleratedOrbit 13 575 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 575) = 3 ^ 7 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_575.1, data_13_575.2]

/-- Complete interval computation for depth 13, residue 576. -/
theorem bounds_13_576 : exactInterval 13 576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_576 : oddCount 576 13 = 5 ∧ acceleratedOrbit 13 576 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 576) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_576.1, data_13_576.2]

/-- Complete interval computation for depth 13, residue 577. -/
theorem bounds_13_577 : exactInterval 13 577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_577 : oddCount 577 13 = 6 ∧ acceleratedOrbit 13 577 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 577) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_577.1, data_13_577.2]

/-- Complete interval computation for depth 13, residue 578. -/
theorem bounds_13_578 : exactInterval 13 578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_578 : oddCount 578 13 = 6 ∧ acceleratedOrbit 13 578 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 578) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_578.1, data_13_578.2]

/-- Complete interval computation for depth 13, residue 579. -/
theorem bounds_13_579 : exactInterval 13 579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_579 : oddCount 579 13 = 6 ∧ acceleratedOrbit 13 579 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 579) = 3 ^ 6 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_579.1, data_13_579.2]

/-- Complete interval computation for depth 13, residue 580. -/
theorem bounds_13_580 : exactInterval 13 580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_580 : oddCount 580 13 = 7 ∧ acceleratedOrbit 13 580 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 580) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_580.1, data_13_580.2]

/-- Complete interval computation for depth 13, residue 581. -/
theorem bounds_13_581 : exactInterval 13 581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_581 : oddCount 581 13 = 7 ∧ acceleratedOrbit 13 581 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 581) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_581.1, data_13_581.2]

/-- Complete interval computation for depth 13, residue 582. -/
theorem bounds_13_582 : exactInterval 13 582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_582 : oddCount 582 13 = 7 ∧ acceleratedOrbit 13 582 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 582) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_582.1, data_13_582.2]

/-- Complete interval computation for depth 13, residue 583. -/
theorem bounds_13_583 : exactInterval 13 583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_583 : oddCount 583 13 = 6 ∧ acceleratedOrbit 13 583 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 583) = 3 ^ 6 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_583.1, data_13_583.2]

/-- Complete interval computation for depth 13, residue 584. -/
theorem bounds_13_584 : exactInterval 13 584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_584 : oddCount 584 13 = 7 ∧ acceleratedOrbit 13 584 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 584) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_584.1, data_13_584.2]

/-- Complete interval computation for depth 13, residue 585. -/
theorem bounds_13_585 : exactInterval 13 585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_585 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 585) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_585 : oddCount 585 13 = 7 ∧ acceleratedOrbit 13 585 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_585 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 585) = 3 ^ 7 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_585.1, data_13_585.2]

/-- Complete interval computation for depth 13, residue 586. -/
theorem bounds_13_586 : exactInterval 13 586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_586 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 586) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_586 : oddCount 586 13 = 7 ∧ acceleratedOrbit 13 586 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_586 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 586) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_586.1, data_13_586.2]

/-- Complete interval computation for depth 13, residue 587. -/
theorem bounds_13_587 : exactInterval 13 587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_587 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 587) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_587 : oddCount 587 13 = 7 ∧ acceleratedOrbit 13 587 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_587 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 587) = 3 ^ 7 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_587.1, data_13_587.2]

end Collatz.Research.StoppingAtlas.Batch0505
