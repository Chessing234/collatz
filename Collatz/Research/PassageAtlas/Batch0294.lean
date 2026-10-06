import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0294

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9601. -/
theorem bounds_15_9601 : exactInterval 15 9601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9601 : oddCount 9601 15 = 9 ∧ acceleratedOrbit 15 9601 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9601) = 3 ^ 9 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9601.1, data_15_9601.2]

/-- Complete interval computation for depth 15, residue 9602. -/
theorem bounds_15_9602 : exactInterval 15 9602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9602 : oddCount 9602 15 = 6 ∧ acceleratedOrbit 15 9602 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9602) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9602.1, data_15_9602.2]

/-- Complete interval computation for depth 15, residue 9603. -/
theorem bounds_15_9603 : exactInterval 15 9603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9603 : oddCount 9603 15 = 6 ∧ acceleratedOrbit 15 9603 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9603) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9603.1, data_15_9603.2]

/-- Complete interval computation for depth 15, residue 9604. -/
theorem bounds_15_9604 : exactInterval 15 9604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9604 : oddCount 9604 15 = 9 ∧ acceleratedOrbit 15 9604 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9604) = 3 ^ 9 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9604.1, data_15_9604.2]

/-- Complete interval computation for depth 15, residue 9605. -/
theorem bounds_15_9605 : exactInterval 15 9605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9605 : oddCount 9605 15 = 9 ∧ acceleratedOrbit 15 9605 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9605) = 3 ^ 9 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9605.1, data_15_9605.2]

/-- Complete interval computation for depth 15, residue 9606. -/
theorem bounds_15_9606 : exactInterval 15 9606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9606 : oddCount 9606 15 = 9 ∧ acceleratedOrbit 15 9606 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9606) = 3 ^ 9 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9606.1, data_15_9606.2]

/-- Complete interval computation for depth 15, residue 9607. -/
theorem bounds_15_9607 : exactInterval 15 9607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9607 : oddCount 9607 15 = 6 ∧ acceleratedOrbit 15 9607 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9607) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9607.1, data_15_9607.2]

/-- Complete interval computation for depth 15, residue 9608. -/
theorem bounds_15_9608 : exactInterval 15 9608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9608 : oddCount 9608 15 = 7 ∧ acceleratedOrbit 15 9608 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9608) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9608.1, data_15_9608.2]

/-- Complete interval computation for depth 15, residue 9609. -/
theorem bounds_15_9609 : exactInterval 15 9609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9609 : oddCount 9609 15 = 8 ∧ acceleratedOrbit 15 9609 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9609) = 3 ^ 8 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9609.1, data_15_9609.2]

/-- Complete interval computation for depth 15, residue 9610. -/
theorem bounds_15_9610 : exactInterval 15 9610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9610 : oddCount 9610 15 = 7 ∧ acceleratedOrbit 15 9610 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9610) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9610.1, data_15_9610.2]

/-- Complete interval computation for depth 15, residue 9611. -/
theorem bounds_15_9611 : exactInterval 15 9611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9611 : oddCount 9611 15 = 9 ∧ acceleratedOrbit 15 9611 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9611) = 3 ^ 9 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9611.1, data_15_9611.2]

/-- Complete interval computation for depth 15, residue 9612. -/
theorem bounds_15_9612 : exactInterval 15 9612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9612 : oddCount 9612 15 = 7 ∧ acceleratedOrbit 15 9612 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9612) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9612.1, data_15_9612.2]

/-- Complete interval computation for depth 15, residue 9613. -/
theorem bounds_15_9613 : exactInterval 15 9613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9613 : oddCount 9613 15 = 7 ∧ acceleratedOrbit 15 9613 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9613) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9613.1, data_15_9613.2]

/-- Complete interval computation for depth 15, residue 9614. -/
theorem bounds_15_9614 : exactInterval 15 9614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9614 : oddCount 9614 15 = 6 ∧ acceleratedOrbit 15 9614 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9614) = 3 ^ 6 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9614.1, data_15_9614.2]

/-- Complete interval computation for depth 15, residue 9615. -/
theorem bounds_15_9615 : exactInterval 15 9615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9615 : oddCount 9615 15 = 6 ∧ acceleratedOrbit 15 9615 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9615) = 3 ^ 6 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9615.1, data_15_9615.2]

/-- Complete interval computation for depth 15, residue 9616. -/
theorem bounds_15_9616 : exactInterval 15 9616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9616 : oddCount 9616 15 = 7 ∧ acceleratedOrbit 15 9616 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9616) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9616.1, data_15_9616.2]

/-- Complete interval computation for depth 15, residue 9617. -/
theorem bounds_15_9617 : exactInterval 15 9617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9617 : oddCount 9617 15 = 7 ∧ acceleratedOrbit 15 9617 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9617) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9617.1, data_15_9617.2]

/-- Complete interval computation for depth 15, residue 9618. -/
theorem bounds_15_9618 : exactInterval 15 9618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9618 : oddCount 9618 15 = 7 ∧ acceleratedOrbit 15 9618 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9618) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9618.1, data_15_9618.2]

/-- Complete interval computation for depth 15, residue 9619. -/
theorem bounds_15_9619 : exactInterval 15 9619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9619 : oddCount 9619 15 = 7 ∧ acceleratedOrbit 15 9619 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9619) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9619.1, data_15_9619.2]

/-- Complete interval computation for depth 15, residue 9620. -/
theorem bounds_15_9620 : exactInterval 15 9620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9620 : oddCount 9620 15 = 7 ∧ acceleratedOrbit 15 9620 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9620) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9620.1, data_15_9620.2]

/-- Complete interval computation for depth 15, residue 9621. -/
theorem bounds_15_9621 : exactInterval 15 9621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9621 : oddCount 9621 15 = 7 ∧ acceleratedOrbit 15 9621 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9621) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9621.1, data_15_9621.2]

/-- Complete interval computation for depth 15, residue 9622. -/
theorem bounds_15_9622 : exactInterval 15 9622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9622 : oddCount 9622 15 = 7 ∧ acceleratedOrbit 15 9622 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9622) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9622.1, data_15_9622.2]

/-- Complete interval computation for depth 15, residue 9623. -/
theorem bounds_15_9623 : exactInterval 15 9623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9623 : oddCount 9623 15 = 7 ∧ acceleratedOrbit 15 9623 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9623) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9623.1, data_15_9623.2]

/-- Complete interval computation for depth 15, residue 9624. -/
theorem bounds_15_9624 : exactInterval 15 9624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9624 : oddCount 9624 15 = 7 ∧ acceleratedOrbit 15 9624 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9624) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9624.1, data_15_9624.2]

/-- Complete interval computation for depth 15, residue 9625. -/
theorem bounds_15_9625 : exactInterval 15 9625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9625 : oddCount 9625 15 = 7 ∧ acceleratedOrbit 15 9625 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9625) = 3 ^ 7 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9625.1, data_15_9625.2]

/-- Complete interval computation for depth 15, residue 9626. -/
theorem bounds_15_9626 : exactInterval 15 9626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9626 : oddCount 9626 15 = 7 ∧ acceleratedOrbit 15 9626 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9626) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9626.1, data_15_9626.2]

/-- Complete interval computation for depth 15, residue 9627. -/
theorem bounds_15_9627 : exactInterval 15 9627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9627 : oddCount 9627 15 = 8 ∧ acceleratedOrbit 15 9627 = 1928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9627) = 3 ^ 8 * m + 1928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9627.1, data_15_9627.2]

/-- Complete interval computation for depth 15, residue 9628. -/
theorem bounds_15_9628 : exactInterval 15 9628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9628 : oddCount 9628 15 = 10 ∧ acceleratedOrbit 15 9628 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9628) = 3 ^ 10 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9628.1, data_15_9628.2]

/-- Complete interval computation for depth 15, residue 9629. -/
theorem bounds_15_9629 : exactInterval 15 9629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9629 : oddCount 9629 15 = 10 ∧ acceleratedOrbit 15 9629 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9629) = 3 ^ 10 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9629.1, data_15_9629.2]

/-- Complete interval computation for depth 15, residue 9630. -/
theorem bounds_15_9630 : exactInterval 15 9630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9630 : oddCount 9630 15 = 10 ∧ acceleratedOrbit 15 9630 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9630) = 3 ^ 10 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9630.1, data_15_9630.2]

/-- Complete interval computation for depth 15, residue 9631. -/
theorem bounds_15_9631 : exactInterval 15 9631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9631 : oddCount 9631 15 = 11 ∧ acceleratedOrbit 15 9631 = 52073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9631) = 3 ^ 11 * m + 52073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9631.1, data_15_9631.2]

/-- Complete interval computation for depth 15, residue 9632. -/
theorem bounds_15_9632 : exactInterval 15 9632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9632 : oddCount 9632 15 = 3 ∧ acceleratedOrbit 15 9632 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9632) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9632.1, data_15_9632.2]

end Collatz.Research.PassageAtlas.Batch0294
