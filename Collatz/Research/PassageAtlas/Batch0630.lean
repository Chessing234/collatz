import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0630

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20611. -/
theorem bounds_15_20611 : exactInterval 15 20611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20611 : oddCount 20611 15 = 9 ∧ acceleratedOrbit 15 20611 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20611) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20611.1, data_15_20611.2]

/-- Complete interval computation for depth 15, residue 20612. -/
theorem bounds_15_20612 : exactInterval 15 20612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20612 : oddCount 20612 15 = 9 ∧ acceleratedOrbit 15 20612 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20612) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20612.1, data_15_20612.2]

/-- Complete interval computation for depth 15, residue 20613. -/
theorem bounds_15_20613 : exactInterval 15 20613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20613 : oddCount 20613 15 = 9 ∧ acceleratedOrbit 15 20613 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20613) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20613.1, data_15_20613.2]

/-- Complete interval computation for depth 15, residue 20614. -/
theorem bounds_15_20614 : exactInterval 15 20614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20614 : oddCount 20614 15 = 9 ∧ acceleratedOrbit 15 20614 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20614) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20614.1, data_15_20614.2]

/-- Complete interval computation for depth 15, residue 20615. -/
theorem bounds_15_20615 : exactInterval 15 20615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20615 : oddCount 20615 15 = 9 ∧ acceleratedOrbit 15 20615 = 12386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20615) = 3 ^ 9 * m + 12386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20615.1, data_15_20615.2]

/-- Complete interval computation for depth 15, residue 20616. -/
theorem bounds_15_20616 : exactInterval 15 20616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20616 : oddCount 20616 15 = 3 ∧ acceleratedOrbit 15 20616 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20616) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20616.1, data_15_20616.2]

/-- Complete interval computation for depth 15, residue 20617. -/
theorem bounds_15_20617 : exactInterval 15 20617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20617 : oddCount 20617 15 = 11 ∧ acceleratedOrbit 15 20617 = 111469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20617) = 3 ^ 11 * m + 111469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20617.1, data_15_20617.2]

/-- Complete interval computation for depth 15, residue 20618. -/
theorem bounds_15_20618 : exactInterval 15 20618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20618 : oddCount 20618 15 = 3 ∧ acceleratedOrbit 15 20618 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20618) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20618.1, data_15_20618.2]

/-- Complete interval computation for depth 15, residue 20619. -/
theorem bounds_15_20619 : exactInterval 15 20619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20619 : oddCount 20619 15 = 9 ∧ acceleratedOrbit 15 20619 = 12388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20619) = 3 ^ 9 * m + 12388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20619.1, data_15_20619.2]

/-- Complete interval computation for depth 15, residue 20620. -/
theorem bounds_15_20620 : exactInterval 15 20620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20620 : oddCount 20620 15 = 3 ∧ acceleratedOrbit 15 20620 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20620) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20620.1, data_15_20620.2]

/-- Complete interval computation for depth 15, residue 20621. -/
theorem bounds_15_20621 : exactInterval 15 20621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20621 : oddCount 20621 15 = 3 ∧ acceleratedOrbit 15 20621 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20621) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20621.1, data_15_20621.2]

/-- Complete interval computation for depth 15, residue 20622. -/
theorem bounds_15_20622 : exactInterval 15 20622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20622 : oddCount 20622 15 = 10 ∧ acceleratedOrbit 15 20622 = 37169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20622) = 3 ^ 10 * m + 37169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20622.1, data_15_20622.2]

/-- Complete interval computation for depth 15, residue 20623. -/
theorem bounds_15_20623 : exactInterval 15 20623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20623 : oddCount 20623 15 = 10 ∧ acceleratedOrbit 15 20623 = 37169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20623) = 3 ^ 10 * m + 37169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20623.1, data_15_20623.2]

/-- Complete interval computation for depth 15, residue 20624. -/
theorem bounds_15_20624 : exactInterval 15 20624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20624 : oddCount 20624 15 = 7 ∧ acceleratedOrbit 15 20624 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20624) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20624.1, data_15_20624.2]

/-- Complete interval computation for depth 15, residue 20625. -/
theorem bounds_15_20625 : exactInterval 15 20625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20625 : oddCount 20625 15 = 11 ∧ acceleratedOrbit 15 20625 = 111536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20625) = 3 ^ 11 * m + 111536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20625.1, data_15_20625.2]

/-- Complete interval computation for depth 15, residue 20626. -/
theorem bounds_15_20626 : exactInterval 15 20626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20626 : oddCount 20626 15 = 11 ∧ acceleratedOrbit 15 20626 = 111536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20626) = 3 ^ 11 * m + 111536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20626.1, data_15_20626.2]

/-- Complete interval computation for depth 15, residue 20627. -/
theorem bounds_15_20627 : exactInterval 15 20627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20627 : oddCount 20627 15 = 11 ∧ acceleratedOrbit 15 20627 = 111536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20627) = 3 ^ 11 * m + 111536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20627.1, data_15_20627.2]

/-- Complete interval computation for depth 15, residue 20628. -/
theorem bounds_15_20628 : exactInterval 15 20628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20628 : oddCount 20628 15 = 7 ∧ acceleratedOrbit 15 20628 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20628) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20628.1, data_15_20628.2]

/-- Complete interval computation for depth 15, residue 20629. -/
theorem bounds_15_20629 : exactInterval 15 20629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20629 : oddCount 20629 15 = 7 ∧ acceleratedOrbit 15 20629 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20629) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20629.1, data_15_20629.2]

/-- Complete interval computation for depth 15, residue 20630. -/
theorem bounds_15_20630 : exactInterval 15 20630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20630 : oddCount 20630 15 = 3 ∧ acceleratedOrbit 15 20630 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20630) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20630.1, data_15_20630.2]

/-- Complete interval computation for depth 15, residue 20631. -/
theorem bounds_15_20631 : exactInterval 15 20631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20631 : oddCount 20631 15 = 3 ∧ acceleratedOrbit 15 20631 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20631) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20631.1, data_15_20631.2]

/-- Complete interval computation for depth 15, residue 20632. -/
theorem bounds_15_20632 : exactInterval 15 20632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20632 : oddCount 20632 15 = 7 ∧ acceleratedOrbit 15 20632 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20632) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20632.1, data_15_20632.2]

/-- Complete interval computation for depth 15, residue 20633. -/
theorem bounds_15_20633 : exactInterval 15 20633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20633 : oddCount 20633 15 = 8 ∧ acceleratedOrbit 15 20633 = 4133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20633) = 3 ^ 8 * m + 4133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20633.1, data_15_20633.2]

/-- Complete interval computation for depth 15, residue 20634. -/
theorem bounds_15_20634 : exactInterval 15 20634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20634 : oddCount 20634 15 = 7 ∧ acceleratedOrbit 15 20634 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20634) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20634.1, data_15_20634.2]

/-- Complete interval computation for depth 15, residue 20635. -/
theorem bounds_15_20635 : exactInterval 15 20635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20635 : oddCount 20635 15 = 8 ∧ acceleratedOrbit 15 20635 = 4132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20635) = 3 ^ 8 * m + 4132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20635.1, data_15_20635.2]

/-- Complete interval computation for depth 15, residue 20636. -/
theorem bounds_15_20636 : exactInterval 15 20636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20636 : oddCount 20636 15 = 7 ∧ acceleratedOrbit 15 20636 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20636) = 3 ^ 7 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20636.1, data_15_20636.2]

/-- Complete interval computation for depth 15, residue 20637. -/
theorem bounds_15_20637 : exactInterval 15 20637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20637 : oddCount 20637 15 = 7 ∧ acceleratedOrbit 15 20637 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20637) = 3 ^ 7 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20637.1, data_15_20637.2]

/-- Complete interval computation for depth 15, residue 20638. -/
theorem bounds_15_20638 : exactInterval 15 20638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20638 : oddCount 20638 15 = 7 ∧ acceleratedOrbit 15 20638 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20638) = 3 ^ 7 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20638.1, data_15_20638.2]

/-- Complete interval computation for depth 15, residue 20639. -/
theorem bounds_15_20639 : exactInterval 15 20639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20639 : oddCount 20639 15 = 12 ∧ acceleratedOrbit 15 20639 = 334748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20639) = 3 ^ 12 * m + 334748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20639.1, data_15_20639.2]

/-- Complete interval computation for depth 15, residue 20640. -/
theorem bounds_15_20640 : exactInterval 15 20640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20640 : oddCount 20640 15 = 5 ∧ acceleratedOrbit 15 20640 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20640) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20640.1, data_15_20640.2]

/-- Complete interval computation for depth 15, residue 20641. -/
theorem bounds_15_20641 : exactInterval 15 20641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20641 : oddCount 20641 15 = 9 ∧ acceleratedOrbit 15 20641 = 12401 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20641) = 3 ^ 9 * m + 12401 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20641.1, data_15_20641.2]

/-- Complete interval computation for depth 15, residue 20642. -/
theorem bounds_15_20642 : exactInterval 15 20642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20642 : oddCount 20642 15 = 7 ∧ acceleratedOrbit 15 20642 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20642) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20642.1, data_15_20642.2]

end Collatz.Research.PassageAtlas.Batch0630
