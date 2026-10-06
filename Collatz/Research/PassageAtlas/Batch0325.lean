import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0325

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10616. -/
theorem bounds_15_10616 : exactInterval 15 10616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10616 : oddCount 10616 15 = 8 ∧ acceleratedOrbit 15 10616 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10616) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10616.1, data_15_10616.2]

/-- Complete interval computation for depth 15, residue 10617. -/
theorem bounds_15_10617 : exactInterval 15 10617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10617 : oddCount 10617 15 = 12 ∧ acceleratedOrbit 15 10617 = 172226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10617) = 3 ^ 12 * m + 172226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10617.1, data_15_10617.2]

/-- Complete interval computation for depth 15, residue 10618. -/
theorem bounds_15_10618 : exactInterval 15 10618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10618 : oddCount 10618 15 = 8 ∧ acceleratedOrbit 15 10618 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10618) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10618.1, data_15_10618.2]

/-- Complete interval computation for depth 15, residue 10619. -/
theorem bounds_15_10619 : exactInterval 15 10619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10619 : oddCount 10619 15 = 10 ∧ acceleratedOrbit 15 10619 = 19142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10619) = 3 ^ 10 * m + 19142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10619.1, data_15_10619.2]

/-- Complete interval computation for depth 15, residue 10620. -/
theorem bounds_15_10620 : exactInterval 15 10620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10620 : oddCount 10620 15 = 8 ∧ acceleratedOrbit 15 10620 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10620) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10620.1, data_15_10620.2]

/-- Complete interval computation for depth 15, residue 10621. -/
theorem bounds_15_10621 : exactInterval 15 10621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10621 : oddCount 10621 15 = 8 ∧ acceleratedOrbit 15 10621 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10621) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10621.1, data_15_10621.2]

/-- Complete interval computation for depth 15, residue 10622. -/
theorem bounds_15_10622 : exactInterval 15 10622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10622 : oddCount 10622 15 = 9 ∧ acceleratedOrbit 15 10622 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10622) = 3 ^ 9 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10622.1, data_15_10622.2]

/-- Complete interval computation for depth 15, residue 10623. -/
theorem bounds_15_10623 : exactInterval 15 10623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10623 : oddCount 10623 15 = 9 ∧ acceleratedOrbit 15 10623 = 6382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10623) = 3 ^ 9 * m + 6382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10623.1, data_15_10623.2]

/-- Complete interval computation for depth 15, residue 10624. -/
theorem bounds_15_10624 : exactInterval 15 10624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10624 : oddCount 10624 15 = 6 ∧ acceleratedOrbit 15 10624 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10624) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10624.1, data_15_10624.2]

/-- Complete interval computation for depth 15, residue 10625. -/
theorem bounds_15_10625 : exactInterval 15 10625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10625 : oddCount 10625 15 = 7 ∧ acceleratedOrbit 15 10625 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10625) = 3 ^ 7 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10625.1, data_15_10625.2]

/-- Complete interval computation for depth 15, residue 10626. -/
theorem bounds_15_10626 : exactInterval 15 10626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10626 : oddCount 10626 15 = 8 ∧ acceleratedOrbit 15 10626 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10626) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10626.1, data_15_10626.2]

/-- Complete interval computation for depth 15, residue 10627. -/
theorem bounds_15_10627 : exactInterval 15 10627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10627 : oddCount 10627 15 = 8 ∧ acceleratedOrbit 15 10627 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10627) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10627.1, data_15_10627.2]

/-- Complete interval computation for depth 15, residue 10628. -/
theorem bounds_15_10628 : exactInterval 15 10628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10628 : oddCount 10628 15 = 8 ∧ acceleratedOrbit 15 10628 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10628) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10628.1, data_15_10628.2]

/-- Complete interval computation for depth 15, residue 10629. -/
theorem bounds_15_10629 : exactInterval 15 10629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10629 : oddCount 10629 15 = 8 ∧ acceleratedOrbit 15 10629 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10629) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10629.1, data_15_10629.2]

/-- Complete interval computation for depth 15, residue 10630. -/
theorem bounds_15_10630 : exactInterval 15 10630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10630 : oddCount 10630 15 = 8 ∧ acceleratedOrbit 15 10630 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10630) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10630.1, data_15_10630.2]

/-- Complete interval computation for depth 15, residue 10631. -/
theorem bounds_15_10631 : exactInterval 15 10631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10631 : oddCount 10631 15 = 8 ∧ acceleratedOrbit 15 10631 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10631) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10631.1, data_15_10631.2]

/-- Complete interval computation for depth 15, residue 10632. -/
theorem bounds_15_10632 : exactInterval 15 10632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10632 : oddCount 10632 15 = 6 ∧ acceleratedOrbit 15 10632 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10632) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10632.1, data_15_10632.2]

/-- Complete interval computation for depth 15, residue 10633. -/
theorem bounds_15_10633 : exactInterval 15 10633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10633 : oddCount 10633 15 = 9 ∧ acceleratedOrbit 15 10633 = 6389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10633) = 3 ^ 9 * m + 6389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10633.1, data_15_10633.2]

/-- Complete interval computation for depth 15, residue 10634. -/
theorem bounds_15_10634 : exactInterval 15 10634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10634 : oddCount 10634 15 = 6 ∧ acceleratedOrbit 15 10634 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10634) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10634.1, data_15_10634.2]

/-- Complete interval computation for depth 15, residue 10635. -/
theorem bounds_15_10635 : exactInterval 15 10635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10635 : oddCount 10635 15 = 7 ∧ acceleratedOrbit 15 10635 = 710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10635) = 3 ^ 7 * m + 710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10635.1, data_15_10635.2]

/-- Complete interval computation for depth 15, residue 10636. -/
theorem bounds_15_10636 : exactInterval 15 10636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10636 : oddCount 10636 15 = 6 ∧ acceleratedOrbit 15 10636 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10636) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10636.1, data_15_10636.2]

/-- Complete interval computation for depth 15, residue 10637. -/
theorem bounds_15_10637 : exactInterval 15 10637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10637 : oddCount 10637 15 = 6 ∧ acceleratedOrbit 15 10637 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10637) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10637.1, data_15_10637.2]

/-- Complete interval computation for depth 15, residue 10638. -/
theorem bounds_15_10638 : exactInterval 15 10638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10638 : oddCount 10638 15 = 8 ∧ acceleratedOrbit 15 10638 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10638) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10638.1, data_15_10638.2]

/-- Complete interval computation for depth 15, residue 10639. -/
theorem bounds_15_10639 : exactInterval 15 10639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10639 : oddCount 10639 15 = 8 ∧ acceleratedOrbit 15 10639 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10639) = 3 ^ 8 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10639.1, data_15_10639.2]

/-- Complete interval computation for depth 15, residue 10640. -/
theorem bounds_15_10640 : exactInterval 15 10640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10640 : oddCount 10640 15 = 6 ∧ acceleratedOrbit 15 10640 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10640) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10640.1, data_15_10640.2]

/-- Complete interval computation for depth 15, residue 10641. -/
theorem bounds_15_10641 : exactInterval 15 10641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10641 : oddCount 10641 15 = 5 ∧ acceleratedOrbit 15 10641 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10641) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10641.1, data_15_10641.2]

/-- Complete interval computation for depth 15, residue 10642. -/
theorem bounds_15_10642 : exactInterval 15 10642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10642 : oddCount 10642 15 = 5 ∧ acceleratedOrbit 15 10642 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10642) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10642.1, data_15_10642.2]

/-- Complete interval computation for depth 15, residue 10643. -/
theorem bounds_15_10643 : exactInterval 15 10643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10643 : oddCount 10643 15 = 5 ∧ acceleratedOrbit 15 10643 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10643) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10643.1, data_15_10643.2]

/-- Complete interval computation for depth 15, residue 10644. -/
theorem bounds_15_10644 : exactInterval 15 10644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10644 : oddCount 10644 15 = 6 ∧ acceleratedOrbit 15 10644 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10644) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10644.1, data_15_10644.2]

/-- Complete interval computation for depth 15, residue 10645. -/
theorem bounds_15_10645 : exactInterval 15 10645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10645 : oddCount 10645 15 = 6 ∧ acceleratedOrbit 15 10645 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10645) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10645.1, data_15_10645.2]

/-- Complete interval computation for depth 15, residue 10646. -/
theorem bounds_15_10646 : exactInterval 15 10646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10646 : oddCount 10646 15 = 5 ∧ acceleratedOrbit 15 10646 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10646) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10646.1, data_15_10646.2]

/-- Complete interval computation for depth 15, residue 10647. -/
theorem bounds_15_10647 : exactInterval 15 10647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10647 : oddCount 10647 15 = 5 ∧ acceleratedOrbit 15 10647 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10647) = 3 ^ 5 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10647.1, data_15_10647.2]

/-- Complete interval computation for depth 15, residue 10648. -/
theorem bounds_15_10648 : exactInterval 15 10648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10648 : oddCount 10648 15 = 6 ∧ acceleratedOrbit 15 10648 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10648) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10648.1, data_15_10648.2]

end Collatz.Research.PassageAtlas.Batch0325
