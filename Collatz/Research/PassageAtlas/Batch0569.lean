import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0569

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18612. -/
theorem bounds_15_18612 : exactInterval 15 18612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18612 : oddCount 18612 15 = 6 ∧ acceleratedOrbit 15 18612 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18612) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18612.1, data_15_18612.2]

/-- Complete interval computation for depth 15, residue 18613. -/
theorem bounds_15_18613 : exactInterval 15 18613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18613 : oddCount 18613 15 = 6 ∧ acceleratedOrbit 15 18613 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18613) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18613.1, data_15_18613.2]

/-- Complete interval computation for depth 15, residue 18614. -/
theorem bounds_15_18614 : exactInterval 15 18614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18614 : oddCount 18614 15 = 9 ∧ acceleratedOrbit 15 18614 = 11183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18614) = 3 ^ 9 * m + 11183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18614.1, data_15_18614.2]

/-- Complete interval computation for depth 15, residue 18615. -/
theorem bounds_15_18615 : exactInterval 15 18615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18615 : oddCount 18615 15 = 9 ∧ acceleratedOrbit 15 18615 = 11183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18615) = 3 ^ 9 * m + 11183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18615.1, data_15_18615.2]

/-- Complete interval computation for depth 15, residue 18616. -/
theorem bounds_15_18616 : exactInterval 15 18616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18616 : oddCount 18616 15 = 6 ∧ acceleratedOrbit 15 18616 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18616) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18616.1, data_15_18616.2]

/-- Complete interval computation for depth 15, residue 18617. -/
theorem bounds_15_18617 : exactInterval 15 18617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18617 : oddCount 18617 15 = 7 ∧ acceleratedOrbit 15 18617 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18617) = 3 ^ 7 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18617.1, data_15_18617.2]

/-- Complete interval computation for depth 15, residue 18618. -/
theorem bounds_15_18618 : exactInterval 15 18618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18618 : oddCount 18618 15 = 6 ∧ acceleratedOrbit 15 18618 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18618) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18618.1, data_15_18618.2]

/-- Complete interval computation for depth 15, residue 18619. -/
theorem bounds_15_18619 : exactInterval 15 18619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18619 : oddCount 18619 15 = 9 ∧ acceleratedOrbit 15 18619 = 11186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18619) = 3 ^ 9 * m + 11186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18619.1, data_15_18619.2]

/-- Complete interval computation for depth 15, residue 18620. -/
theorem bounds_15_18620 : exactInterval 15 18620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18620 : oddCount 18620 15 = 9 ∧ acceleratedOrbit 15 18620 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18620) = 3 ^ 9 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18620.1, data_15_18620.2]

/-- Complete interval computation for depth 15, residue 18621. -/
theorem bounds_15_18621 : exactInterval 15 18621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18621 : oddCount 18621 15 = 9 ∧ acceleratedOrbit 15 18621 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18621) = 3 ^ 9 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18621.1, data_15_18621.2]

/-- Complete interval computation for depth 15, residue 18622. -/
theorem bounds_15_18622 : exactInterval 15 18622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18622 : oddCount 18622 15 = 9 ∧ acceleratedOrbit 15 18622 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18622) = 3 ^ 9 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18622.1, data_15_18622.2]

/-- Complete interval computation for depth 15, residue 18623. -/
theorem bounds_15_18623 : exactInterval 15 18623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18623 : oddCount 18623 15 = 7 ∧ acceleratedOrbit 15 18623 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18623) = 3 ^ 7 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18623.1, data_15_18623.2]

/-- Complete interval computation for depth 15, residue 18624. -/
theorem bounds_15_18624 : exactInterval 15 18624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18624 : oddCount 18624 15 = 4 ∧ acceleratedOrbit 15 18624 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18624) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18624.1, data_15_18624.2]

/-- Complete interval computation for depth 15, residue 18625. -/
theorem bounds_15_18625 : exactInterval 15 18625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18625 : oddCount 18625 15 = 7 ∧ acceleratedOrbit 15 18625 = 1244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18625) = 3 ^ 7 * m + 1244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18625.1, data_15_18625.2]

/-- Complete interval computation for depth 15, residue 18626. -/
theorem bounds_15_18626 : exactInterval 15 18626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18626 : oddCount 18626 15 = 7 ∧ acceleratedOrbit 15 18626 = 1244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18626) = 3 ^ 7 * m + 1244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18626.1, data_15_18626.2]

/-- Complete interval computation for depth 15, residue 18627. -/
theorem bounds_15_18627 : exactInterval 15 18627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18627 : oddCount 18627 15 = 7 ∧ acceleratedOrbit 15 18627 = 1244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18627) = 3 ^ 7 * m + 1244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18627.1, data_15_18627.2]

/-- Complete interval computation for depth 15, residue 18628. -/
theorem bounds_15_18628 : exactInterval 15 18628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18628 : oddCount 18628 15 = 6 ∧ acceleratedOrbit 15 18628 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18628) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18628.1, data_15_18628.2]

/-- Complete interval computation for depth 15, residue 18629. -/
theorem bounds_15_18629 : exactInterval 15 18629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18629 : oddCount 18629 15 = 6 ∧ acceleratedOrbit 15 18629 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18629) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18629.1, data_15_18629.2]

/-- Complete interval computation for depth 15, residue 18630. -/
theorem bounds_15_18630 : exactInterval 15 18630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18630 : oddCount 18630 15 = 6 ∧ acceleratedOrbit 15 18630 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18630) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18630.1, data_15_18630.2]

/-- Complete interval computation for depth 15, residue 18631. -/
theorem bounds_15_18631 : exactInterval 15 18631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18631 : oddCount 18631 15 = 8 ∧ acceleratedOrbit 15 18631 = 3731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18631) = 3 ^ 8 * m + 3731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18631.1, data_15_18631.2]

/-- Complete interval computation for depth 15, residue 18632. -/
theorem bounds_15_18632 : exactInterval 15 18632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18632 : oddCount 18632 15 = 6 ∧ acceleratedOrbit 15 18632 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18632) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18632.1, data_15_18632.2]

/-- Complete interval computation for depth 15, residue 18633. -/
theorem bounds_15_18633 : exactInterval 15 18633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18633 : oddCount 18633 15 = 6 ∧ acceleratedOrbit 15 18633 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18633) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18633.1, data_15_18633.2]

/-- Complete interval computation for depth 15, residue 18634. -/
theorem bounds_15_18634 : exactInterval 15 18634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18634 : oddCount 18634 15 = 6 ∧ acceleratedOrbit 15 18634 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18634) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18634.1, data_15_18634.2]

/-- Complete interval computation for depth 15, residue 18635. -/
theorem bounds_15_18635 : exactInterval 15 18635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18635 : oddCount 18635 15 = 9 ∧ acceleratedOrbit 15 18635 = 11198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18635) = 3 ^ 9 * m + 11198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18635.1, data_15_18635.2]

/-- Complete interval computation for depth 15, residue 18636. -/
theorem bounds_15_18636 : exactInterval 15 18636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18636 : oddCount 18636 15 = 6 ∧ acceleratedOrbit 15 18636 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18636) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18636.1, data_15_18636.2]

/-- Complete interval computation for depth 15, residue 18637. -/
theorem bounds_15_18637 : exactInterval 15 18637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18637 : oddCount 18637 15 = 6 ∧ acceleratedOrbit 15 18637 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18637) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18637.1, data_15_18637.2]

/-- Complete interval computation for depth 15, residue 18638. -/
theorem bounds_15_18638 : exactInterval 15 18638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18638 : oddCount 18638 15 = 9 ∧ acceleratedOrbit 15 18638 = 11197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18638) = 3 ^ 9 * m + 11197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18638.1, data_15_18638.2]

/-- Complete interval computation for depth 15, residue 18639. -/
theorem bounds_15_18639 : exactInterval 15 18639 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18639) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18639 : oddCount 18639 15 = 9 ∧ acceleratedOrbit 15 18639 = 11197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18639) = 3 ^ 9 * m + 11197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18639.1, data_15_18639.2]

/-- Complete interval computation for depth 15, residue 18640. -/
theorem bounds_15_18640 : exactInterval 15 18640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18640 : oddCount 18640 15 = 4 ∧ acceleratedOrbit 15 18640 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18640) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18640.1, data_15_18640.2]

/-- Complete interval computation for depth 15, residue 18641. -/
theorem bounds_15_18641 : exactInterval 15 18641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18641 : oddCount 18641 15 = 8 ∧ acceleratedOrbit 15 18641 = 3734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18641) = 3 ^ 8 * m + 3734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18641.1, data_15_18641.2]

/-- Complete interval computation for depth 15, residue 18642. -/
theorem bounds_15_18642 : exactInterval 15 18642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18642 : oddCount 18642 15 = 8 ∧ acceleratedOrbit 15 18642 = 3734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18642) = 3 ^ 8 * m + 3734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18642.1, data_15_18642.2]

/-- Complete interval computation for depth 15, residue 18643. -/
theorem bounds_15_18643 : exactInterval 15 18643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18643 : oddCount 18643 15 = 8 ∧ acceleratedOrbit 15 18643 = 3734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18643) = 3 ^ 8 * m + 3734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18643.1, data_15_18643.2]

end Collatz.Research.PassageAtlas.Batch0569
