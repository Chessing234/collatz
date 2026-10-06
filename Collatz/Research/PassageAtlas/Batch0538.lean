import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0538

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17596. -/
theorem bounds_15_17596 : exactInterval 15 17596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17596 : oddCount 17596 15 = 9 ∧ acceleratedOrbit 15 17596 = 10574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17596) = 3 ^ 9 * m + 10574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17596.1, data_15_17596.2]

/-- Complete interval computation for depth 15, residue 17597. -/
theorem bounds_15_17597 : exactInterval 15 17597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17597 : oddCount 17597 15 = 9 ∧ acceleratedOrbit 15 17597 = 10574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17597) = 3 ^ 9 * m + 10574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17597.1, data_15_17597.2]

/-- Complete interval computation for depth 15, residue 17598. -/
theorem bounds_15_17598 : exactInterval 15 17598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17598 : oddCount 17598 15 = 9 ∧ acceleratedOrbit 15 17598 = 10574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17598) = 3 ^ 9 * m + 10574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17598.1, data_15_17598.2]

/-- Complete interval computation for depth 15, residue 17599. -/
theorem bounds_15_17599 : exactInterval 15 17599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17599 : oddCount 17599 15 = 8 ∧ acceleratedOrbit 15 17599 = 3524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17599) = 3 ^ 8 * m + 3524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17599.1, data_15_17599.2]

/-- Complete interval computation for depth 15, residue 17600. -/
theorem bounds_15_17600 : exactInterval 15 17600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17600 : oddCount 17600 15 = 6 ∧ acceleratedOrbit 15 17600 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17600) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17600.1, data_15_17600.2]

/-- Complete interval computation for depth 15, residue 17601. -/
theorem bounds_15_17601 : exactInterval 15 17601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17601 : oddCount 17601 15 = 8 ∧ acceleratedOrbit 15 17601 = 3527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17601) = 3 ^ 8 * m + 3527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17601.1, data_15_17601.2]

/-- Complete interval computation for depth 15, residue 17602. -/
theorem bounds_15_17602 : exactInterval 15 17602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17602 : oddCount 17602 15 = 8 ∧ acceleratedOrbit 15 17602 = 3527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17602) = 3 ^ 8 * m + 3527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17602.1, data_15_17602.2]

/-- Complete interval computation for depth 15, residue 17603. -/
theorem bounds_15_17603 : exactInterval 15 17603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17603 : oddCount 17603 15 = 8 ∧ acceleratedOrbit 15 17603 = 3527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17603) = 3 ^ 8 * m + 3527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17603.1, data_15_17603.2]

/-- Complete interval computation for depth 15, residue 17604. -/
theorem bounds_15_17604 : exactInterval 15 17604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17604 : oddCount 17604 15 = 7 ∧ acceleratedOrbit 15 17604 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17604) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17604.1, data_15_17604.2]

/-- Complete interval computation for depth 15, residue 17605. -/
theorem bounds_15_17605 : exactInterval 15 17605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17605 : oddCount 17605 15 = 7 ∧ acceleratedOrbit 15 17605 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17605) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17605.1, data_15_17605.2]

/-- Complete interval computation for depth 15, residue 17606. -/
theorem bounds_15_17606 : exactInterval 15 17606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17606 : oddCount 17606 15 = 7 ∧ acceleratedOrbit 15 17606 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17606) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17606.1, data_15_17606.2]

/-- Complete interval computation for depth 15, residue 17607. -/
theorem bounds_15_17607 : exactInterval 15 17607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17607 : oddCount 17607 15 = 8 ∧ acceleratedOrbit 15 17607 = 3527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17607) = 3 ^ 8 * m + 3527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17607.1, data_15_17607.2]

/-- Complete interval computation for depth 15, residue 17608. -/
theorem bounds_15_17608 : exactInterval 15 17608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17608 : oddCount 17608 15 = 7 ∧ acceleratedOrbit 15 17608 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17608) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17608.1, data_15_17608.2]

/-- Complete interval computation for depth 15, residue 17609. -/
theorem bounds_15_17609 : exactInterval 15 17609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17609 : oddCount 17609 15 = 6 ∧ acceleratedOrbit 15 17609 = 392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17609) = 3 ^ 6 * m + 392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17609.1, data_15_17609.2]

/-- Complete interval computation for depth 15, residue 17610. -/
theorem bounds_15_17610 : exactInterval 15 17610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17610 : oddCount 17610 15 = 7 ∧ acceleratedOrbit 15 17610 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17610) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17610.1, data_15_17610.2]

/-- Complete interval computation for depth 15, residue 17611. -/
theorem bounds_15_17611 : exactInterval 15 17611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17611 : oddCount 17611 15 = 6 ∧ acceleratedOrbit 15 17611 = 392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17611) = 3 ^ 6 * m + 392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17611.1, data_15_17611.2]

/-- Complete interval computation for depth 15, residue 17612. -/
theorem bounds_15_17612 : exactInterval 15 17612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17612 : oddCount 17612 15 = 7 ∧ acceleratedOrbit 15 17612 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17612) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17612.1, data_15_17612.2]

/-- Complete interval computation for depth 15, residue 17613. -/
theorem bounds_15_17613 : exactInterval 15 17613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17613 : oddCount 17613 15 = 7 ∧ acceleratedOrbit 15 17613 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17613) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17613.1, data_15_17613.2]

/-- Complete interval computation for depth 15, residue 17614. -/
theorem bounds_15_17614 : exactInterval 15 17614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17614 : oddCount 17614 15 = 9 ∧ acceleratedOrbit 15 17614 = 10583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17614) = 3 ^ 9 * m + 10583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17614.1, data_15_17614.2]

/-- Complete interval computation for depth 15, residue 17615. -/
theorem bounds_15_17615 : exactInterval 15 17615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17615 : oddCount 17615 15 = 9 ∧ acceleratedOrbit 15 17615 = 10583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17615) = 3 ^ 9 * m + 10583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17615.1, data_15_17615.2]

/-- Complete interval computation for depth 15, residue 17616. -/
theorem bounds_15_17616 : exactInterval 15 17616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17616 : oddCount 17616 15 = 6 ∧ acceleratedOrbit 15 17616 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17616) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17616.1, data_15_17616.2]

/-- Complete interval computation for depth 15, residue 17617. -/
theorem bounds_15_17617 : exactInterval 15 17617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17617 : oddCount 17617 15 = 9 ∧ acceleratedOrbit 15 17617 = 10586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17617) = 3 ^ 9 * m + 10586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17617.1, data_15_17617.2]

/-- Complete interval computation for depth 15, residue 17618. -/
theorem bounds_15_17618 : exactInterval 15 17618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17618 : oddCount 17618 15 = 9 ∧ acceleratedOrbit 15 17618 = 10586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17618) = 3 ^ 9 * m + 10586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17618.1, data_15_17618.2]

/-- Complete interval computation for depth 15, residue 17619. -/
theorem bounds_15_17619 : exactInterval 15 17619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17619 : oddCount 17619 15 = 9 ∧ acceleratedOrbit 15 17619 = 10586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17619) = 3 ^ 9 * m + 10586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17619.1, data_15_17619.2]

/-- Complete interval computation for depth 15, residue 17620. -/
theorem bounds_15_17620 : exactInterval 15 17620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17620 : oddCount 17620 15 = 6 ∧ acceleratedOrbit 15 17620 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17620) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17620.1, data_15_17620.2]

/-- Complete interval computation for depth 15, residue 17621. -/
theorem bounds_15_17621 : exactInterval 15 17621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17621 : oddCount 17621 15 = 6 ∧ acceleratedOrbit 15 17621 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17621) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17621.1, data_15_17621.2]

/-- Complete interval computation for depth 15, residue 17622. -/
theorem bounds_15_17622 : exactInterval 15 17622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17622 : oddCount 17622 15 = 8 ∧ acceleratedOrbit 15 17622 = 3530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17622) = 3 ^ 8 * m + 3530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17622.1, data_15_17622.2]

/-- Complete interval computation for depth 15, residue 17623. -/
theorem bounds_15_17623 : exactInterval 15 17623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17623 : oddCount 17623 15 = 8 ∧ acceleratedOrbit 15 17623 = 3530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17623) = 3 ^ 8 * m + 3530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17623.1, data_15_17623.2]

/-- Complete interval computation for depth 15, residue 17624. -/
theorem bounds_15_17624 : exactInterval 15 17624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17624 : oddCount 17624 15 = 7 ∧ acceleratedOrbit 15 17624 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17624) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17624.1, data_15_17624.2]

/-- Complete interval computation for depth 15, residue 17625. -/
theorem bounds_15_17625 : exactInterval 15 17625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17625 : oddCount 17625 15 = 7 ∧ acceleratedOrbit 15 17625 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17625) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17625.1, data_15_17625.2]

/-- Complete interval computation for depth 15, residue 17626. -/
theorem bounds_15_17626 : exactInterval 15 17626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17626 : oddCount 17626 15 = 7 ∧ acceleratedOrbit 15 17626 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17626) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17626.1, data_15_17626.2]

/-- Complete interval computation for depth 15, residue 17627. -/
theorem bounds_15_17627 : exactInterval 15 17627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17627 : oddCount 17627 15 = 8 ∧ acceleratedOrbit 15 17627 = 3530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17627) = 3 ^ 8 * m + 3530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17627.1, data_15_17627.2]

/-- Complete interval computation for depth 15, residue 17628. -/
theorem bounds_15_17628 : exactInterval 15 17628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17628 : oddCount 17628 15 = 7 ∧ acceleratedOrbit 15 17628 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17628) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17628.1, data_15_17628.2]

end Collatz.Research.PassageAtlas.Batch0538
