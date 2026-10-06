import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0995

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32571. -/
theorem bounds_15_32571 : exactInterval 15 32571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32571 : oddCount 32571 15 = 8 ∧ acceleratedOrbit 15 32571 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32571) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32571.1, data_15_32571.2]

/-- Complete interval computation for depth 15, residue 32572. -/
theorem bounds_15_32572 : exactInterval 15 32572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32572 : oddCount 32572 15 = 8 ∧ acceleratedOrbit 15 32572 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32572) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32572.1, data_15_32572.2]

/-- Complete interval computation for depth 15, residue 32573. -/
theorem bounds_15_32573 : exactInterval 15 32573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32573 : oddCount 32573 15 = 8 ∧ acceleratedOrbit 15 32573 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32573) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32573.1, data_15_32573.2]

/-- Complete interval computation for depth 15, residue 32574. -/
theorem bounds_15_32574 : exactInterval 15 32574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32574 : oddCount 32574 15 = 9 ∧ acceleratedOrbit 15 32574 = 19568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32574) = 3 ^ 9 * m + 19568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32574.1, data_15_32574.2]

/-- Complete interval computation for depth 15, residue 32575. -/
theorem bounds_15_32575 : exactInterval 15 32575 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32575) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32575 : oddCount 32575 15 = 9 ∧ acceleratedOrbit 15 32575 = 19568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32575) = 3 ^ 9 * m + 19568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32575.1, data_15_32575.2]

/-- Complete interval computation for depth 15, residue 32576. -/
theorem bounds_15_32576 : exactInterval 15 32576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32576 : oddCount 32576 15 = 7 ∧ acceleratedOrbit 15 32576 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32576) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32576.1, data_15_32576.2]

/-- Complete interval computation for depth 15, residue 32577. -/
theorem bounds_15_32577 : exactInterval 15 32577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32577 : oddCount 32577 15 = 7 ∧ acceleratedOrbit 15 32577 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32577) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32577.1, data_15_32577.2]

/-- Complete interval computation for depth 15, residue 32578. -/
theorem bounds_15_32578 : exactInterval 15 32578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32578 : oddCount 32578 15 = 6 ∧ acceleratedOrbit 15 32578 = 725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32578) = 3 ^ 6 * m + 725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32578.1, data_15_32578.2]

/-- Complete interval computation for depth 15, residue 32579. -/
theorem bounds_15_32579 : exactInterval 15 32579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32579 : oddCount 32579 15 = 6 ∧ acceleratedOrbit 15 32579 = 725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32579) = 3 ^ 6 * m + 725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32579.1, data_15_32579.2]

/-- Complete interval computation for depth 15, residue 32580. -/
theorem bounds_15_32580 : exactInterval 15 32580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32580 : oddCount 32580 15 = 7 ∧ acceleratedOrbit 15 32580 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32580) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32580.1, data_15_32580.2]

/-- Complete interval computation for depth 15, residue 32581. -/
theorem bounds_15_32581 : exactInterval 15 32581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32581 : oddCount 32581 15 = 7 ∧ acceleratedOrbit 15 32581 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32581) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32581.1, data_15_32581.2]

/-- Complete interval computation for depth 15, residue 32582. -/
theorem bounds_15_32582 : exactInterval 15 32582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32582 : oddCount 32582 15 = 7 ∧ acceleratedOrbit 15 32582 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32582) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32582.1, data_15_32582.2]

/-- Complete interval computation for depth 15, residue 32583. -/
theorem bounds_15_32583 : exactInterval 15 32583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32583 : oddCount 32583 15 = 9 ∧ acceleratedOrbit 15 32583 = 19574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32583) = 3 ^ 9 * m + 19574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32583.1, data_15_32583.2]

/-- Complete interval computation for depth 15, residue 32584. -/
theorem bounds_15_32584 : exactInterval 15 32584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32584 : oddCount 32584 15 = 8 ∧ acceleratedOrbit 15 32584 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32584) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32584.1, data_15_32584.2]

/-- Complete interval computation for depth 15, residue 32585. -/
theorem bounds_15_32585 : exactInterval 15 32585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32585 : oddCount 32585 15 = 6 ∧ acceleratedOrbit 15 32585 = 725 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32585) = 3 ^ 6 * m + 725 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32585.1, data_15_32585.2]

/-- Complete interval computation for depth 15, residue 32586. -/
theorem bounds_15_32586 : exactInterval 15 32586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32586 : oddCount 32586 15 = 8 ∧ acceleratedOrbit 15 32586 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32586) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32586.1, data_15_32586.2]

/-- Complete interval computation for depth 15, residue 32587. -/
theorem bounds_15_32587 : exactInterval 15 32587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32587 : oddCount 32587 15 = 7 ∧ acceleratedOrbit 15 32587 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32587) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32587.1, data_15_32587.2]

/-- Complete interval computation for depth 15, residue 32588. -/
theorem bounds_15_32588 : exactInterval 15 32588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32588 : oddCount 32588 15 = 8 ∧ acceleratedOrbit 15 32588 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32588) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32588.1, data_15_32588.2]

/-- Complete interval computation for depth 15, residue 32589. -/
theorem bounds_15_32589 : exactInterval 15 32589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32589 : oddCount 32589 15 = 8 ∧ acceleratedOrbit 15 32589 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32589) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32589.1, data_15_32589.2]

/-- Complete interval computation for depth 15, residue 32590. -/
theorem bounds_15_32590 : exactInterval 15 32590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32590 : oddCount 32590 15 = 8 ∧ acceleratedOrbit 15 32590 = 6526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32590) = 3 ^ 8 * m + 6526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32590.1, data_15_32590.2]

/-- Complete interval computation for depth 15, residue 32591. -/
theorem bounds_15_32591 : exactInterval 15 32591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32591 : oddCount 32591 15 = 8 ∧ acceleratedOrbit 15 32591 = 6526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32591) = 3 ^ 8 * m + 6526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32591.1, data_15_32591.2]

/-- Complete interval computation for depth 15, residue 32592. -/
theorem bounds_15_32592 : exactInterval 15 32592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32592 : oddCount 32592 15 = 7 ∧ acceleratedOrbit 15 32592 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32592) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32592.1, data_15_32592.2]

/-- Complete interval computation for depth 15, residue 32593. -/
theorem bounds_15_32593 : exactInterval 15 32593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32593 : oddCount 32593 15 = 8 ∧ acceleratedOrbit 15 32593 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32593) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32593.1, data_15_32593.2]

/-- Complete interval computation for depth 15, residue 32594. -/
theorem bounds_15_32594 : exactInterval 15 32594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32594 : oddCount 32594 15 = 10 ∧ acceleratedOrbit 15 32594 = 58742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32594) = 3 ^ 10 * m + 58742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32594.1, data_15_32594.2]

/-- Complete interval computation for depth 15, residue 32595. -/
theorem bounds_15_32595 : exactInterval 15 32595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32595 : oddCount 32595 15 = 10 ∧ acceleratedOrbit 15 32595 = 58742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32595) = 3 ^ 10 * m + 58742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32595.1, data_15_32595.2]

/-- Complete interval computation for depth 15, residue 32596. -/
theorem bounds_15_32596 : exactInterval 15 32596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32596 : oddCount 32596 15 = 7 ∧ acceleratedOrbit 15 32596 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32596) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32596.1, data_15_32596.2]

/-- Complete interval computation for depth 15, residue 32597. -/
theorem bounds_15_32597 : exactInterval 15 32597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32597 : oddCount 32597 15 = 7 ∧ acceleratedOrbit 15 32597 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32597) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32597.1, data_15_32597.2]

/-- Complete interval computation for depth 15, residue 32598. -/
theorem bounds_15_32598 : exactInterval 15 32598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32598 : oddCount 32598 15 = 7 ∧ acceleratedOrbit 15 32598 = 2176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32598) = 3 ^ 7 * m + 2176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32598.1, data_15_32598.2]

/-- Complete interval computation for depth 15, residue 32599. -/
theorem bounds_15_32599 : exactInterval 15 32599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32599 : oddCount 32599 15 = 7 ∧ acceleratedOrbit 15 32599 = 2176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32599) = 3 ^ 7 * m + 2176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32599.1, data_15_32599.2]

/-- Complete interval computation for depth 15, residue 32600. -/
theorem bounds_15_32600 : exactInterval 15 32600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32600 : oddCount 32600 15 = 9 ∧ acceleratedOrbit 15 32600 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32600) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32600.1, data_15_32600.2]

/-- Complete interval computation for depth 15, residue 32601. -/
theorem bounds_15_32601 : exactInterval 15 32601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32601 : oddCount 32601 15 = 7 ∧ acceleratedOrbit 15 32601 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32601) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32601.1, data_15_32601.2]

/-- Complete interval computation for depth 15, residue 32602. -/
theorem bounds_15_32602 : exactInterval 15 32602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32602 : oddCount 32602 15 = 9 ∧ acceleratedOrbit 15 32602 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32602) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32602.1, data_15_32602.2]

/-- Complete interval computation for depth 15, residue 32603. -/
theorem bounds_15_32603 : exactInterval 15 32603 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32603) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32603 : oddCount 32603 15 = 9 ∧ acceleratedOrbit 15 32603 = 19585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32603) = 3 ^ 9 * m + 19585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32603.1, data_15_32603.2]

end Collatz.Research.PassageAtlas.Batch0995
