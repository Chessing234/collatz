import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0598

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19562. -/
theorem bounds_15_19562 : exactInterval 15 19562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19562 : oddCount 19562 15 = 4 ∧ acceleratedOrbit 15 19562 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19562) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19562.1, data_15_19562.2]

/-- Complete interval computation for depth 15, residue 19563. -/
theorem bounds_15_19563 : exactInterval 15 19563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19563 : oddCount 19563 15 = 9 ∧ acceleratedOrbit 15 19563 = 11753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19563) = 3 ^ 9 * m + 11753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19563.1, data_15_19563.2]

/-- Complete interval computation for depth 15, residue 19564. -/
theorem bounds_15_19564 : exactInterval 15 19564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19564 : oddCount 19564 15 = 9 ∧ acceleratedOrbit 15 19564 = 11755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19564) = 3 ^ 9 * m + 11755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19564.1, data_15_19564.2]

/-- Complete interval computation for depth 15, residue 19565. -/
theorem bounds_15_19565 : exactInterval 15 19565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19565 : oddCount 19565 15 = 9 ∧ acceleratedOrbit 15 19565 = 11755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19565) = 3 ^ 9 * m + 11755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19565.1, data_15_19565.2]

/-- Complete interval computation for depth 15, residue 19566. -/
theorem bounds_15_19566 : exactInterval 15 19566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19566 : oddCount 19566 15 = 9 ∧ acceleratedOrbit 15 19566 = 11755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19566) = 3 ^ 9 * m + 11755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19566.1, data_15_19566.2]

/-- Complete interval computation for depth 15, residue 19567. -/
theorem bounds_15_19567 : exactInterval 15 19567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19567 : oddCount 19567 15 = 10 ∧ acceleratedOrbit 15 19567 = 35263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19567) = 3 ^ 10 * m + 35263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19567.1, data_15_19567.2]

/-- Complete interval computation for depth 15, residue 19568. -/
theorem bounds_15_19568 : exactInterval 15 19568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19568 : oddCount 19568 15 = 6 ∧ acceleratedOrbit 15 19568 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19568) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19568.1, data_15_19568.2]

/-- Complete interval computation for depth 15, residue 19569. -/
theorem bounds_15_19569 : exactInterval 15 19569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19569 : oddCount 19569 15 = 4 ∧ acceleratedOrbit 15 19569 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19569) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19569.1, data_15_19569.2]

/-- Complete interval computation for depth 15, residue 19570. -/
theorem bounds_15_19570 : exactInterval 15 19570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19570 : oddCount 19570 15 = 7 ∧ acceleratedOrbit 15 19570 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19570) = 3 ^ 7 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19570.1, data_15_19570.2]

/-- Complete interval computation for depth 15, residue 19571. -/
theorem bounds_15_19571 : exactInterval 15 19571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19571 : oddCount 19571 15 = 7 ∧ acceleratedOrbit 15 19571 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19571) = 3 ^ 7 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19571.1, data_15_19571.2]

/-- Complete interval computation for depth 15, residue 19572. -/
theorem bounds_15_19572 : exactInterval 15 19572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19572 : oddCount 19572 15 = 6 ∧ acceleratedOrbit 15 19572 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19572) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19572.1, data_15_19572.2]

/-- Complete interval computation for depth 15, residue 19573. -/
theorem bounds_15_19573 : exactInterval 15 19573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19573 : oddCount 19573 15 = 6 ∧ acceleratedOrbit 15 19573 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19573) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19573.1, data_15_19573.2]

/-- Complete interval computation for depth 15, residue 19574. -/
theorem bounds_15_19574 : exactInterval 15 19574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19574 : oddCount 19574 15 = 7 ∧ acceleratedOrbit 15 19574 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19574) = 3 ^ 7 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19574.1, data_15_19574.2]

/-- Complete interval computation for depth 15, residue 19575. -/
theorem bounds_15_19575 : exactInterval 15 19575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19575 : oddCount 19575 15 = 7 ∧ acceleratedOrbit 15 19575 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19575) = 3 ^ 7 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19575.1, data_15_19575.2]

/-- Complete interval computation for depth 15, residue 19576. -/
theorem bounds_15_19576 : exactInterval 15 19576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19576 : oddCount 19576 15 = 6 ∧ acceleratedOrbit 15 19576 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19576) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19576.1, data_15_19576.2]

/-- Complete interval computation for depth 15, residue 19577. -/
theorem bounds_15_19577 : exactInterval 15 19577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19577 : oddCount 19577 15 = 9 ∧ acceleratedOrbit 15 19577 = 11762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19577) = 3 ^ 9 * m + 11762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19577.1, data_15_19577.2]

/-- Complete interval computation for depth 15, residue 19578. -/
theorem bounds_15_19578 : exactInterval 15 19578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19578 : oddCount 19578 15 = 6 ∧ acceleratedOrbit 15 19578 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19578) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19578.1, data_15_19578.2]

/-- Complete interval computation for depth 15, residue 19579. -/
theorem bounds_15_19579 : exactInterval 15 19579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19579 : oddCount 19579 15 = 7 ∧ acceleratedOrbit 15 19579 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19579) = 3 ^ 7 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19579.1, data_15_19579.2]

/-- Complete interval computation for depth 15, residue 19580. -/
theorem bounds_15_19580 : exactInterval 15 19580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19580 : oddCount 19580 15 = 9 ∧ acceleratedOrbit 15 19580 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19580) = 3 ^ 9 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19580.1, data_15_19580.2]

/-- Complete interval computation for depth 15, residue 19581. -/
theorem bounds_15_19581 : exactInterval 15 19581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19581 : oddCount 19581 15 = 9 ∧ acceleratedOrbit 15 19581 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19581) = 3 ^ 9 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19581.1, data_15_19581.2]

/-- Complete interval computation for depth 15, residue 19582. -/
theorem bounds_15_19582 : exactInterval 15 19582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19582 : oddCount 19582 15 = 9 ∧ acceleratedOrbit 15 19582 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19582) = 3 ^ 9 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19582.1, data_15_19582.2]

/-- Complete interval computation for depth 15, residue 19583. -/
theorem bounds_15_19583 : exactInterval 15 19583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19583 : oddCount 19583 15 = 12 ∧ acceleratedOrbit 15 19583 = 317621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19583) = 3 ^ 12 * m + 317621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19583.1, data_15_19583.2]

/-- Complete interval computation for depth 15, residue 19584. -/
theorem bounds_15_19584 : exactInterval 15 19584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19584 : oddCount 19584 15 = 4 ∧ acceleratedOrbit 15 19584 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19584) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19584.1, data_15_19584.2]

/-- Complete interval computation for depth 15, residue 19585. -/
theorem bounds_15_19585 : exactInterval 15 19585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19585 : oddCount 19585 15 = 9 ∧ acceleratedOrbit 15 19585 = 11767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19585) = 3 ^ 9 * m + 11767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19585.1, data_15_19585.2]

/-- Complete interval computation for depth 15, residue 19586. -/
theorem bounds_15_19586 : exactInterval 15 19586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19586 : oddCount 19586 15 = 7 ∧ acceleratedOrbit 15 19586 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19586) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19586.1, data_15_19586.2]

/-- Complete interval computation for depth 15, residue 19587. -/
theorem bounds_15_19587 : exactInterval 15 19587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19587 : oddCount 19587 15 = 7 ∧ acceleratedOrbit 15 19587 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19587) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19587.1, data_15_19587.2]

/-- Complete interval computation for depth 15, residue 19588. -/
theorem bounds_15_19588 : exactInterval 15 19588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19588 : oddCount 19588 15 = 7 ∧ acceleratedOrbit 15 19588 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19588) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19588.1, data_15_19588.2]

/-- Complete interval computation for depth 15, residue 19589. -/
theorem bounds_15_19589 : exactInterval 15 19589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19589 : oddCount 19589 15 = 7 ∧ acceleratedOrbit 15 19589 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19589) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19589.1, data_15_19589.2]

/-- Complete interval computation for depth 15, residue 19590. -/
theorem bounds_15_19590 : exactInterval 15 19590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19590 : oddCount 19590 15 = 7 ∧ acceleratedOrbit 15 19590 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19590) = 3 ^ 7 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19590.1, data_15_19590.2]

/-- Complete interval computation for depth 15, residue 19591. -/
theorem bounds_15_19591 : exactInterval 15 19591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19591 : oddCount 19591 15 = 9 ∧ acceleratedOrbit 15 19591 = 11771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19591) = 3 ^ 9 * m + 11771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19591.1, data_15_19591.2]

/-- Complete interval computation for depth 15, residue 19592. -/
theorem bounds_15_19592 : exactInterval 15 19592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19592 : oddCount 19592 15 = 5 ∧ acceleratedOrbit 15 19592 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19592) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19592.1, data_15_19592.2]

/-- Complete interval computation for depth 15, residue 19593. -/
theorem bounds_15_19593 : exactInterval 15 19593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19593 : oddCount 19593 15 = 10 ∧ acceleratedOrbit 15 19593 = 35311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19593) = 3 ^ 10 * m + 35311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19593.1, data_15_19593.2]

/-- Complete interval computation for depth 15, residue 19594. -/
theorem bounds_15_19594 : exactInterval 15 19594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19594 : oddCount 19594 15 = 5 ∧ acceleratedOrbit 15 19594 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19594) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19594.1, data_15_19594.2]

end Collatz.Research.PassageAtlas.Batch0598
