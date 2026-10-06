import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0354

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11567. -/
theorem bounds_15_11567 : exactInterval 15 11567 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11567) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11567 : oddCount 11567 15 = 9 ∧ acceleratedOrbit 15 11567 = 6949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11567) = 3 ^ 9 * m + 6949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11567.1, data_15_11567.2]

/-- Complete interval computation for depth 15, residue 11568. -/
theorem bounds_15_11568 : exactInterval 15 11568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11568 : oddCount 11568 15 = 5 ∧ acceleratedOrbit 15 11568 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11568) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11568.1, data_15_11568.2]

/-- Complete interval computation for depth 15, residue 11569. -/
theorem bounds_15_11569 : exactInterval 15 11569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11569 : oddCount 11569 15 = 9 ∧ acceleratedOrbit 15 11569 = 6956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11569) = 3 ^ 9 * m + 6956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11569.1, data_15_11569.2]

/-- Complete interval computation for depth 15, residue 11570. -/
theorem bounds_15_11570 : exactInterval 15 11570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11570 : oddCount 11570 15 = 9 ∧ acceleratedOrbit 15 11570 = 6956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11570) = 3 ^ 9 * m + 6956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11570.1, data_15_11570.2]

/-- Complete interval computation for depth 15, residue 11571. -/
theorem bounds_15_11571 : exactInterval 15 11571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11571 : oddCount 11571 15 = 9 ∧ acceleratedOrbit 15 11571 = 6956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11571) = 3 ^ 9 * m + 6956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11571.1, data_15_11571.2]

/-- Complete interval computation for depth 15, residue 11572. -/
theorem bounds_15_11572 : exactInterval 15 11572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11572 : oddCount 11572 15 = 5 ∧ acceleratedOrbit 15 11572 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11572) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11572.1, data_15_11572.2]

/-- Complete interval computation for depth 15, residue 11573. -/
theorem bounds_15_11573 : exactInterval 15 11573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11573 : oddCount 11573 15 = 5 ∧ acceleratedOrbit 15 11573 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11573) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11573.1, data_15_11573.2]

/-- Complete interval computation for depth 15, residue 11574. -/
theorem bounds_15_11574 : exactInterval 15 11574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11574 : oddCount 11574 15 = 8 ∧ acceleratedOrbit 15 11574 = 2318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11574) = 3 ^ 8 * m + 2318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11574.1, data_15_11574.2]

/-- Complete interval computation for depth 15, residue 11575. -/
theorem bounds_15_11575 : exactInterval 15 11575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11575 : oddCount 11575 15 = 8 ∧ acceleratedOrbit 15 11575 = 2318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11575) = 3 ^ 8 * m + 2318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11575.1, data_15_11575.2]

/-- Complete interval computation for depth 15, residue 11576. -/
theorem bounds_15_11576 : exactInterval 15 11576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11576 : oddCount 11576 15 = 8 ∧ acceleratedOrbit 15 11576 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11576) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11576.1, data_15_11576.2]

/-- Complete interval computation for depth 15, residue 11577. -/
theorem bounds_15_11577 : exactInterval 15 11577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11577 : oddCount 11577 15 = 11 ∧ acceleratedOrbit 15 11577 = 62603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11577) = 3 ^ 11 * m + 62603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11577.1, data_15_11577.2]

/-- Complete interval computation for depth 15, residue 11578. -/
theorem bounds_15_11578 : exactInterval 15 11578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11578 : oddCount 11578 15 = 8 ∧ acceleratedOrbit 15 11578 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11578) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11578.1, data_15_11578.2]

/-- Complete interval computation for depth 15, residue 11579. -/
theorem bounds_15_11579 : exactInterval 15 11579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11579 : oddCount 11579 15 = 5 ∧ acceleratedOrbit 15 11579 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11579) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11579.1, data_15_11579.2]

/-- Complete interval computation for depth 15, residue 11580. -/
theorem bounds_15_11580 : exactInterval 15 11580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11580 : oddCount 11580 15 = 8 ∧ acceleratedOrbit 15 11580 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11580) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11580.1, data_15_11580.2]

/-- Complete interval computation for depth 15, residue 11581. -/
theorem bounds_15_11581 : exactInterval 15 11581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11581 : oddCount 11581 15 = 8 ∧ acceleratedOrbit 15 11581 = 2321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11581) = 3 ^ 8 * m + 2321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11581.1, data_15_11581.2]

/-- Complete interval computation for depth 15, residue 11582. -/
theorem bounds_15_11582 : exactInterval 15 11582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11582 : oddCount 11582 15 = 11 ∧ acceleratedOrbit 15 11582 = 62626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11582) = 3 ^ 11 * m + 62626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11582.1, data_15_11582.2]

/-- Complete interval computation for depth 15, residue 11583. -/
theorem bounds_15_11583 : exactInterval 15 11583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11583 : oddCount 11583 15 = 11 ∧ acceleratedOrbit 15 11583 = 62626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11583) = 3 ^ 11 * m + 62626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11583.1, data_15_11583.2]

/-- Complete interval computation for depth 15, residue 11584. -/
theorem bounds_15_11584 : exactInterval 15 11584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11584 : oddCount 11584 15 = 3 ∧ acceleratedOrbit 15 11584 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11584) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11584.1, data_15_11584.2]

/-- Complete interval computation for depth 15, residue 11585. -/
theorem bounds_15_11585 : exactInterval 15 11585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11585 : oddCount 11585 15 = 5 ∧ acceleratedOrbit 15 11585 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11585) = 3 ^ 5 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11585.1, data_15_11585.2]

/-- Complete interval computation for depth 15, residue 11586. -/
theorem bounds_15_11586 : exactInterval 15 11586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11586 : oddCount 11586 15 = 9 ∧ acceleratedOrbit 15 11586 = 6965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11586) = 3 ^ 9 * m + 6965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11586.1, data_15_11586.2]

/-- Complete interval computation for depth 15, residue 11587. -/
theorem bounds_15_11587 : exactInterval 15 11587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11587 : oddCount 11587 15 = 9 ∧ acceleratedOrbit 15 11587 = 6965 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11587) = 3 ^ 9 * m + 6965 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11587.1, data_15_11587.2]

/-- Complete interval computation for depth 15, residue 11588. -/
theorem bounds_15_11588 : exactInterval 15 11588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11588 : oddCount 11588 15 = 8 ∧ acceleratedOrbit 15 11588 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11588) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11588.1, data_15_11588.2]

/-- Complete interval computation for depth 15, residue 11589. -/
theorem bounds_15_11589 : exactInterval 15 11589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11589 : oddCount 11589 15 = 8 ∧ acceleratedOrbit 15 11589 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11589) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11589.1, data_15_11589.2]

/-- Complete interval computation for depth 15, residue 11590. -/
theorem bounds_15_11590 : exactInterval 15 11590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11590 : oddCount 11590 15 = 8 ∧ acceleratedOrbit 15 11590 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11590) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11590.1, data_15_11590.2]

/-- Complete interval computation for depth 15, residue 11591. -/
theorem bounds_15_11591 : exactInterval 15 11591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11591 : oddCount 11591 15 = 10 ∧ acceleratedOrbit 15 11591 = 20891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11591) = 3 ^ 10 * m + 20891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11591.1, data_15_11591.2]

/-- Complete interval computation for depth 15, residue 11592. -/
theorem bounds_15_11592 : exactInterval 15 11592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11592 : oddCount 11592 15 = 8 ∧ acceleratedOrbit 15 11592 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11592) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11592.1, data_15_11592.2]

/-- Complete interval computation for depth 15, residue 11593. -/
theorem bounds_15_11593 : exactInterval 15 11593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11593 : oddCount 11593 15 = 11 ∧ acceleratedOrbit 15 11593 = 62693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11593) = 3 ^ 11 * m + 62693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11593.1, data_15_11593.2]

/-- Complete interval computation for depth 15, residue 11594. -/
theorem bounds_15_11594 : exactInterval 15 11594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11594 : oddCount 11594 15 = 8 ∧ acceleratedOrbit 15 11594 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11594) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11594.1, data_15_11594.2]

/-- Complete interval computation for depth 15, residue 11595. -/
theorem bounds_15_11595 : exactInterval 15 11595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11595 : oddCount 11595 15 = 8 ∧ acceleratedOrbit 15 11595 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11595) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11595.1, data_15_11595.2]

/-- Complete interval computation for depth 15, residue 11596. -/
theorem bounds_15_11596 : exactInterval 15 11596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11596 : oddCount 11596 15 = 8 ∧ acceleratedOrbit 15 11596 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11596) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11596.1, data_15_11596.2]

/-- Complete interval computation for depth 15, residue 11597. -/
theorem bounds_15_11597 : exactInterval 15 11597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11597 : oddCount 11597 15 = 8 ∧ acceleratedOrbit 15 11597 = 2324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11597) = 3 ^ 8 * m + 2324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11597.1, data_15_11597.2]

/-- Complete interval computation for depth 15, residue 11598. -/
theorem bounds_15_11598 : exactInterval 15 11598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11598 : oddCount 11598 15 = 8 ∧ acceleratedOrbit 15 11598 = 2323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11598) = 3 ^ 8 * m + 2323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11598.1, data_15_11598.2]

end Collatz.Research.PassageAtlas.Batch0354
