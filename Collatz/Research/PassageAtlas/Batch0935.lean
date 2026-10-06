import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0935

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30605. -/
theorem bounds_15_30605 : exactInterval 15 30605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30605 : oddCount 30605 15 = 4 ∧ acceleratedOrbit 15 30605 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30605) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30605.1, data_15_30605.2]

/-- Complete interval computation for depth 15, residue 30606. -/
theorem bounds_15_30606 : exactInterval 15 30606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30606 : oddCount 30606 15 = 11 ∧ acceleratedOrbit 15 30606 = 165482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30606) = 3 ^ 11 * m + 165482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30606.1, data_15_30606.2]

/-- Complete interval computation for depth 15, residue 30607. -/
theorem bounds_15_30607 : exactInterval 15 30607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30607 : oddCount 30607 15 = 11 ∧ acceleratedOrbit 15 30607 = 165482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30607) = 3 ^ 11 * m + 165482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30607.1, data_15_30607.2]

/-- Complete interval computation for depth 15, residue 30608. -/
theorem bounds_15_30608 : exactInterval 15 30608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30608 : oddCount 30608 15 = 7 ∧ acceleratedOrbit 15 30608 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30608) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30608.1, data_15_30608.2]

/-- Complete interval computation for depth 15, residue 30609. -/
theorem bounds_15_30609 : exactInterval 15 30609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30609 : oddCount 30609 15 = 8 ∧ acceleratedOrbit 15 30609 = 6131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30609) = 3 ^ 8 * m + 6131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30609.1, data_15_30609.2]

/-- Complete interval computation for depth 15, residue 30610. -/
theorem bounds_15_30610 : exactInterval 15 30610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30610 : oddCount 30610 15 = 8 ∧ acceleratedOrbit 15 30610 = 6131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30610) = 3 ^ 8 * m + 6131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30610.1, data_15_30610.2]

/-- Complete interval computation for depth 15, residue 30611. -/
theorem bounds_15_30611 : exactInterval 15 30611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30611 : oddCount 30611 15 = 8 ∧ acceleratedOrbit 15 30611 = 6131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30611) = 3 ^ 8 * m + 6131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30611.1, data_15_30611.2]

/-- Complete interval computation for depth 15, residue 30612. -/
theorem bounds_15_30612 : exactInterval 15 30612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30612 : oddCount 30612 15 = 7 ∧ acceleratedOrbit 15 30612 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30612) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30612.1, data_15_30612.2]

/-- Complete interval computation for depth 15, residue 30613. -/
theorem bounds_15_30613 : exactInterval 15 30613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30613 : oddCount 30613 15 = 7 ∧ acceleratedOrbit 15 30613 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30613) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30613.1, data_15_30613.2]

/-- Complete interval computation for depth 15, residue 30614. -/
theorem bounds_15_30614 : exactInterval 15 30614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30614 : oddCount 30614 15 = 7 ∧ acceleratedOrbit 15 30614 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30614) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30614.1, data_15_30614.2]

/-- Complete interval computation for depth 15, residue 30615. -/
theorem bounds_15_30615 : exactInterval 15 30615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30615 : oddCount 30615 15 = 7 ∧ acceleratedOrbit 15 30615 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30615) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30615.1, data_15_30615.2]

/-- Complete interval computation for depth 15, residue 30616. -/
theorem bounds_15_30616 : exactInterval 15 30616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30616 : oddCount 30616 15 = 7 ∧ acceleratedOrbit 15 30616 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30616) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30616.1, data_15_30616.2]

/-- Complete interval computation for depth 15, residue 30617. -/
theorem bounds_15_30617 : exactInterval 15 30617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30617 : oddCount 30617 15 = 7 ∧ acceleratedOrbit 15 30617 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30617) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30617.1, data_15_30617.2]

/-- Complete interval computation for depth 15, residue 30618. -/
theorem bounds_15_30618 : exactInterval 15 30618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30618 : oddCount 30618 15 = 7 ∧ acceleratedOrbit 15 30618 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30618) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30618.1, data_15_30618.2]

/-- Complete interval computation for depth 15, residue 30619. -/
theorem bounds_15_30619 : exactInterval 15 30619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30619 : oddCount 30619 15 = 10 ∧ acceleratedOrbit 15 30619 = 55181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30619) = 3 ^ 10 * m + 55181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30619.1, data_15_30619.2]

/-- Complete interval computation for depth 15, residue 30620. -/
theorem bounds_15_30620 : exactInterval 15 30620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30620 : oddCount 30620 15 = 7 ∧ acceleratedOrbit 15 30620 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30620) = 3 ^ 7 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30620.1, data_15_30620.2]

/-- Complete interval computation for depth 15, residue 30621. -/
theorem bounds_15_30621 : exactInterval 15 30621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30621 : oddCount 30621 15 = 7 ∧ acceleratedOrbit 15 30621 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30621) = 3 ^ 7 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30621.1, data_15_30621.2]

/-- Complete interval computation for depth 15, residue 30622. -/
theorem bounds_15_30622 : exactInterval 15 30622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30622 : oddCount 30622 15 = 7 ∧ acceleratedOrbit 15 30622 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30622) = 3 ^ 7 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30622.1, data_15_30622.2]

/-- Complete interval computation for depth 15, residue 30623. -/
theorem bounds_15_30623 : exactInterval 15 30623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30623 : oddCount 30623 15 = 10 ∧ acceleratedOrbit 15 30623 = 55187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30623) = 3 ^ 10 * m + 55187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30623.1, data_15_30623.2]

/-- Complete interval computation for depth 15, residue 30624. -/
theorem bounds_15_30624 : exactInterval 15 30624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30624 : oddCount 30624 15 = 7 ∧ acceleratedOrbit 15 30624 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30624) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30624.1, data_15_30624.2]

/-- Complete interval computation for depth 15, residue 30625. -/
theorem bounds_15_30625 : exactInterval 15 30625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30625 : oddCount 30625 15 = 7 ∧ acceleratedOrbit 15 30625 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30625) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30625.1, data_15_30625.2]

/-- Complete interval computation for depth 15, residue 30626. -/
theorem bounds_15_30626 : exactInterval 15 30626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30626 : oddCount 30626 15 = 7 ∧ acceleratedOrbit 15 30626 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30626) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30626.1, data_15_30626.2]

/-- Complete interval computation for depth 15, residue 30627. -/
theorem bounds_15_30627 : exactInterval 15 30627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30627 : oddCount 30627 15 = 7 ∧ acceleratedOrbit 15 30627 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30627) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30627.1, data_15_30627.2]

/-- Complete interval computation for depth 15, residue 30628. -/
theorem bounds_15_30628 : exactInterval 15 30628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30628 : oddCount 30628 15 = 8 ∧ acceleratedOrbit 15 30628 = 6134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30628) = 3 ^ 8 * m + 6134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30628.1, data_15_30628.2]

/-- Complete interval computation for depth 15, residue 30629. -/
theorem bounds_15_30629 : exactInterval 15 30629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30629 : oddCount 30629 15 = 8 ∧ acceleratedOrbit 15 30629 = 6134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30629) = 3 ^ 8 * m + 6134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30629.1, data_15_30629.2]

/-- Complete interval computation for depth 15, residue 30630. -/
theorem bounds_15_30630 : exactInterval 15 30630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30630 : oddCount 30630 15 = 8 ∧ acceleratedOrbit 15 30630 = 6134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30630) = 3 ^ 8 * m + 6134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30630.1, data_15_30630.2]

/-- Complete interval computation for depth 15, residue 30631. -/
theorem bounds_15_30631 : exactInterval 15 30631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30631 : oddCount 30631 15 = 11 ∧ acceleratedOrbit 15 30631 = 165604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30631) = 3 ^ 11 * m + 165604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30631.1, data_15_30631.2]

/-- Complete interval computation for depth 15, residue 30632. -/
theorem bounds_15_30632 : exactInterval 15 30632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30632 : oddCount 30632 15 = 7 ∧ acceleratedOrbit 15 30632 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30632) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30632.1, data_15_30632.2]

/-- Complete interval computation for depth 15, residue 30633. -/
theorem bounds_15_30633 : exactInterval 15 30633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30633 : oddCount 30633 15 = 12 ∧ acceleratedOrbit 15 30633 = 496844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30633) = 3 ^ 12 * m + 496844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30633.1, data_15_30633.2]

/-- Complete interval computation for depth 15, residue 30634. -/
theorem bounds_15_30634 : exactInterval 15 30634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30634 : oddCount 30634 15 = 7 ∧ acceleratedOrbit 15 30634 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30634) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30634.1, data_15_30634.2]

/-- Complete interval computation for depth 15, residue 30635. -/
theorem bounds_15_30635 : exactInterval 15 30635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30635 : oddCount 30635 15 = 9 ∧ acceleratedOrbit 15 30635 = 18404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30635) = 3 ^ 9 * m + 18404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30635.1, data_15_30635.2]

/-- Complete interval computation for depth 15, residue 30636. -/
theorem bounds_15_30636 : exactInterval 15 30636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30636 : oddCount 30636 15 = 9 ∧ acceleratedOrbit 15 30636 = 18407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30636) = 3 ^ 9 * m + 18407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30636.1, data_15_30636.2]

/-- Complete interval computation for depth 15, residue 30637. -/
theorem bounds_15_30637 : exactInterval 15 30637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30637 : oddCount 30637 15 = 9 ∧ acceleratedOrbit 15 30637 = 18407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30637) = 3 ^ 9 * m + 18407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30637.1, data_15_30637.2]

end Collatz.Research.PassageAtlas.Batch0935
