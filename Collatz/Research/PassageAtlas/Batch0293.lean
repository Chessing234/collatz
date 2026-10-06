import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0293

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9568. -/
theorem bounds_15_9568 : exactInterval 15 9568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9568 : oddCount 9568 15 = 6 ∧ acceleratedOrbit 15 9568 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9568) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9568.1, data_15_9568.2]

/-- Complete interval computation for depth 15, residue 9569. -/
theorem bounds_15_9569 : exactInterval 15 9569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9569 : oddCount 9569 15 = 10 ∧ acceleratedOrbit 15 9569 = 17252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9569) = 3 ^ 10 * m + 17252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9569.1, data_15_9569.2]

/-- Complete interval computation for depth 15, residue 9570. -/
theorem bounds_15_9570 : exactInterval 15 9570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9570 : oddCount 9570 15 = 7 ∧ acceleratedOrbit 15 9570 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9570) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9570.1, data_15_9570.2]

/-- Complete interval computation for depth 15, residue 9571. -/
theorem bounds_15_9571 : exactInterval 15 9571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9571 : oddCount 9571 15 = 7 ∧ acceleratedOrbit 15 9571 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9571) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9571.1, data_15_9571.2]

/-- Complete interval computation for depth 15, residue 9572. -/
theorem bounds_15_9572 : exactInterval 15 9572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9572 : oddCount 9572 15 = 7 ∧ acceleratedOrbit 15 9572 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9572) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9572.1, data_15_9572.2]

/-- Complete interval computation for depth 15, residue 9573. -/
theorem bounds_15_9573 : exactInterval 15 9573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9573 : oddCount 9573 15 = 7 ∧ acceleratedOrbit 15 9573 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9573) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9573.1, data_15_9573.2]

/-- Complete interval computation for depth 15, residue 9574. -/
theorem bounds_15_9574 : exactInterval 15 9574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9574 : oddCount 9574 15 = 7 ∧ acceleratedOrbit 15 9574 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9574) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9574.1, data_15_9574.2]

/-- Complete interval computation for depth 15, residue 9575. -/
theorem bounds_15_9575 : exactInterval 15 9575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9575 : oddCount 9575 15 = 10 ∧ acceleratedOrbit 15 9575 = 17257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9575) = 3 ^ 10 * m + 17257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9575.1, data_15_9575.2]

/-- Complete interval computation for depth 15, residue 9576. -/
theorem bounds_15_9576 : exactInterval 15 9576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9576 : oddCount 9576 15 = 6 ∧ acceleratedOrbit 15 9576 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9576) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9576.1, data_15_9576.2]

/-- Complete interval computation for depth 15, residue 9577. -/
theorem bounds_15_9577 : exactInterval 15 9577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9577 : oddCount 9577 15 = 8 ∧ acceleratedOrbit 15 9577 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9577) = 3 ^ 8 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9577.1, data_15_9577.2]

/-- Complete interval computation for depth 15, residue 9578. -/
theorem bounds_15_9578 : exactInterval 15 9578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9578 : oddCount 9578 15 = 6 ∧ acceleratedOrbit 15 9578 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9578) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9578.1, data_15_9578.2]

/-- Complete interval computation for depth 15, residue 9579. -/
theorem bounds_15_9579 : exactInterval 15 9579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9579 : oddCount 9579 15 = 8 ∧ acceleratedOrbit 15 9579 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9579) = 3 ^ 8 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9579.1, data_15_9579.2]

/-- Complete interval computation for depth 15, residue 9580. -/
theorem bounds_15_9580 : exactInterval 15 9580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9580 : oddCount 9580 15 = 7 ∧ acceleratedOrbit 15 9580 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9580) = 3 ^ 7 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9580.1, data_15_9580.2]

/-- Complete interval computation for depth 15, residue 9581. -/
theorem bounds_15_9581 : exactInterval 15 9581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9581 : oddCount 9581 15 = 7 ∧ acceleratedOrbit 15 9581 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9581) = 3 ^ 7 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9581.1, data_15_9581.2]

/-- Complete interval computation for depth 15, residue 9582. -/
theorem bounds_15_9582 : exactInterval 15 9582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9582 : oddCount 9582 15 = 7 ∧ acceleratedOrbit 15 9582 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9582) = 3 ^ 7 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9582.1, data_15_9582.2]

/-- Complete interval computation for depth 15, residue 9583. -/
theorem bounds_15_9583 : exactInterval 15 9583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9583 : oddCount 9583 15 = 10 ∧ acceleratedOrbit 15 9583 = 17273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9583) = 3 ^ 10 * m + 17273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9583.1, data_15_9583.2]

/-- Complete interval computation for depth 15, residue 9584. -/
theorem bounds_15_9584 : exactInterval 15 9584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9584 : oddCount 9584 15 = 6 ∧ acceleratedOrbit 15 9584 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9584) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9584.1, data_15_9584.2]

/-- Complete interval computation for depth 15, residue 9585. -/
theorem bounds_15_9585 : exactInterval 15 9585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9585 : oddCount 9585 15 = 6 ∧ acceleratedOrbit 15 9585 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9585) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9585.1, data_15_9585.2]

/-- Complete interval computation for depth 15, residue 9586. -/
theorem bounds_15_9586 : exactInterval 15 9586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9586 : oddCount 9586 15 = 7 ∧ acceleratedOrbit 15 9586 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9586) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9586.1, data_15_9586.2]

/-- Complete interval computation for depth 15, residue 9587. -/
theorem bounds_15_9587 : exactInterval 15 9587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9587 : oddCount 9587 15 = 7 ∧ acceleratedOrbit 15 9587 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9587) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9587.1, data_15_9587.2]

/-- Complete interval computation for depth 15, residue 9588. -/
theorem bounds_15_9588 : exactInterval 15 9588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9588 : oddCount 9588 15 = 6 ∧ acceleratedOrbit 15 9588 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9588) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9588.1, data_15_9588.2]

/-- Complete interval computation for depth 15, residue 9589. -/
theorem bounds_15_9589 : exactInterval 15 9589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9589 : oddCount 9589 15 = 6 ∧ acceleratedOrbit 15 9589 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9589) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9589.1, data_15_9589.2]

/-- Complete interval computation for depth 15, residue 9590. -/
theorem bounds_15_9590 : exactInterval 15 9590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9590 : oddCount 9590 15 = 9 ∧ acceleratedOrbit 15 9590 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9590) = 3 ^ 9 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9590.1, data_15_9590.2]

/-- Complete interval computation for depth 15, residue 9591. -/
theorem bounds_15_9591 : exactInterval 15 9591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9591 : oddCount 9591 15 = 9 ∧ acceleratedOrbit 15 9591 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9591) = 3 ^ 9 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9591.1, data_15_9591.2]

/-- Complete interval computation for depth 15, residue 9592. -/
theorem bounds_15_9592 : exactInterval 15 9592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9592 : oddCount 9592 15 = 7 ∧ acceleratedOrbit 15 9592 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9592) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9592.1, data_15_9592.2]

/-- Complete interval computation for depth 15, residue 9593. -/
theorem bounds_15_9593 : exactInterval 15 9593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9593 : oddCount 9593 15 = 10 ∧ acceleratedOrbit 15 9593 = 17291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9593) = 3 ^ 10 * m + 17291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9593.1, data_15_9593.2]

/-- Complete interval computation for depth 15, residue 9594. -/
theorem bounds_15_9594 : exactInterval 15 9594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9594 : oddCount 9594 15 = 7 ∧ acceleratedOrbit 15 9594 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9594) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9594.1, data_15_9594.2]

/-- Complete interval computation for depth 15, residue 9595. -/
theorem bounds_15_9595 : exactInterval 15 9595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9595 : oddCount 9595 15 = 7 ∧ acceleratedOrbit 15 9595 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9595) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9595.1, data_15_9595.2]

/-- Complete interval computation for depth 15, residue 9596. -/
theorem bounds_15_9596 : exactInterval 15 9596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9596 : oddCount 9596 15 = 7 ∧ acceleratedOrbit 15 9596 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9596) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9596.1, data_15_9596.2]

/-- Complete interval computation for depth 15, residue 9597. -/
theorem bounds_15_9597 : exactInterval 15 9597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9597 : oddCount 9597 15 = 7 ∧ acceleratedOrbit 15 9597 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9597) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9597.1, data_15_9597.2]

/-- Complete interval computation for depth 15, residue 9598. -/
theorem bounds_15_9598 : exactInterval 15 9598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9598 : oddCount 9598 15 = 10 ∧ acceleratedOrbit 15 9598 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9598) = 3 ^ 10 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9598.1, data_15_9598.2]

/-- Complete interval computation for depth 15, residue 9599. -/
theorem bounds_15_9599 : exactInterval 15 9599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9599 : oddCount 9599 15 = 10 ∧ acceleratedOrbit 15 9599 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9599) = 3 ^ 10 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9599.1, data_15_9599.2]

/-- Complete interval computation for depth 15, residue 9600. -/
theorem bounds_15_9600 : exactInterval 15 9600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9600 : oddCount 9600 15 = 3 ∧ acceleratedOrbit 15 9600 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9600) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9600.1, data_15_9600.2]

end Collatz.Research.PassageAtlas.Batch0293
