import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0105

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 573. -/
theorem bounds_11_573 : exactInterval 11 573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_573 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 573) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_573 : oddCount 573 11 = 6 ∧ acceleratedOrbit 11 573 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_573 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 573) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_573.1, data_11_573.2]

/-- Complete interval computation for depth 11, residue 574. -/
theorem bounds_11_574 : exactInterval 11 574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_574 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 574) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_574 : oddCount 574 11 = 6 ∧ acceleratedOrbit 11 574 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_574 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 574) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_574.1, data_11_574.2]

/-- Complete interval computation for depth 11, residue 575. -/
theorem bounds_11_575 : exactInterval 11 575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_575 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 575) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_575 : oddCount 575 11 = 6 ∧ acceleratedOrbit 11 575 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_575 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 575) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_575.1, data_11_575.2]

/-- Complete interval computation for depth 11, residue 576. -/
theorem bounds_11_576 : exactInterval 11 576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_576 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 576) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_576 : oddCount 576 11 = 4 ∧ acceleratedOrbit 11 576 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_576 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 576) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_576.1, data_11_576.2]

/-- Complete interval computation for depth 11, residue 577. -/
theorem bounds_11_577 : exactInterval 11 577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_577 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 577) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_577 : oddCount 577 11 = 4 ∧ acceleratedOrbit 11 577 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_577 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 577) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_577.1, data_11_577.2]

/-- Complete interval computation for depth 11, residue 578. -/
theorem bounds_11_578 : exactInterval 11 578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_578 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 578) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_578 : oddCount 578 11 = 4 ∧ acceleratedOrbit 11 578 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_578 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 578) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_578.1, data_11_578.2]

/-- Complete interval computation for depth 11, residue 579. -/
theorem bounds_11_579 : exactInterval 11 579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_579 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 579) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_579 : oddCount 579 11 = 4 ∧ acceleratedOrbit 11 579 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_579 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 579) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_579.1, data_11_579.2]

/-- Complete interval computation for depth 11, residue 580. -/
theorem bounds_11_580 : exactInterval 11 580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_580 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 580) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_580 : oddCount 580 11 = 5 ∧ acceleratedOrbit 11 580 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_580 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 580) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_580.1, data_11_580.2]

/-- Complete interval computation for depth 11, residue 581. -/
theorem bounds_11_581 : exactInterval 11 581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_581 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 581) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_581 : oddCount 581 11 = 5 ∧ acceleratedOrbit 11 581 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_581 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 581) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_581.1, data_11_581.2]

/-- Complete interval computation for depth 11, residue 582. -/
theorem bounds_11_582 : exactInterval 11 582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_582 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 582) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_582 : oddCount 582 11 = 5 ∧ acceleratedOrbit 11 582 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_582 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 582) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_582.1, data_11_582.2]

/-- Complete interval computation for depth 11, residue 583. -/
theorem bounds_11_583 : exactInterval 11 583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_583 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 583) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_583 : oddCount 583 11 = 6 ∧ acceleratedOrbit 11 583 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_583 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 583) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_583.1, data_11_583.2]

/-- Complete interval computation for depth 11, residue 584. -/
theorem bounds_11_584 : exactInterval 11 584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_584 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 584) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_584 : oddCount 584 11 = 5 ∧ acceleratedOrbit 11 584 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_584 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 584) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_584.1, data_11_584.2]

/-- Complete interval computation for depth 11, residue 585. -/
theorem bounds_11_585 : exactInterval 11 585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_585 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 585) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_585 : oddCount 585 11 = 6 ∧ acceleratedOrbit 11 585 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_585 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 585) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_585.1, data_11_585.2]

/-- Complete interval computation for depth 11, residue 586. -/
theorem bounds_11_586 : exactInterval 11 586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_586 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 586) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_586 : oddCount 586 11 = 5 ∧ acceleratedOrbit 11 586 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_586 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 586) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_586.1, data_11_586.2]

/-- Complete interval computation for depth 11, residue 587. -/
theorem bounds_11_587 : exactInterval 11 587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_587 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 587) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_587 : oddCount 587 11 = 5 ∧ acceleratedOrbit 11 587 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_587 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 587) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_587.1, data_11_587.2]

end Collatz.Research.StoppingAtlas.Batch0105
