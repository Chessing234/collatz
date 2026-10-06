import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0703

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3614. -/
theorem bounds_13_3614 : exactInterval 13 3614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3614 : oddCount 3614 13 = 6 ∧ acceleratedOrbit 13 3614 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3614) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3614.1, data_13_3614.2]

/-- Complete interval computation for depth 13, residue 3615. -/
theorem bounds_13_3615 : exactInterval 13 3615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3615 : oddCount 3615 13 = 9 ∧ acceleratedOrbit 13 3615 = 8689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3615) = 3 ^ 9 * m + 8689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3615.1, data_13_3615.2]

/-- Complete interval computation for depth 13, residue 3616. -/
theorem bounds_13_3616 : exactInterval 13 3616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3616 : oddCount 3616 13 = 2 ∧ acceleratedOrbit 13 3616 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3616) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3616.1, data_13_3616.2]

/-- Complete interval computation for depth 13, residue 3617. -/
theorem bounds_13_3617 : exactInterval 13 3617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3617 : oddCount 3617 13 = 7 ∧ acceleratedOrbit 13 3617 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3617) = 3 ^ 7 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3617.1, data_13_3617.2]

/-- Complete interval computation for depth 13, residue 3618. -/
theorem bounds_13_3618 : exactInterval 13 3618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3618 : oddCount 3618 13 = 7 ∧ acceleratedOrbit 13 3618 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3618) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3618.1, data_13_3618.2]

/-- Complete interval computation for depth 13, residue 3619. -/
theorem bounds_13_3619 : exactInterval 13 3619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3619 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3619) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3619 : oddCount 3619 13 = 7 ∧ acceleratedOrbit 13 3619 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3619 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3619) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3619.1, data_13_3619.2]

/-- Complete interval computation for depth 13, residue 3620. -/
theorem bounds_13_3620 : exactInterval 13 3620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3620 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3620) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3620 : oddCount 3620 13 = 8 ∧ acceleratedOrbit 13 3620 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3620 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3620) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3620.1, data_13_3620.2]

/-- Complete interval computation for depth 13, residue 3621. -/
theorem bounds_13_3621 : exactInterval 13 3621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3621 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3621) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3621 : oddCount 3621 13 = 8 ∧ acceleratedOrbit 13 3621 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3621 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3621) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3621.1, data_13_3621.2]

/-- Complete interval computation for depth 13, residue 3622. -/
theorem bounds_13_3622 : exactInterval 13 3622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3622 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3622) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3622 : oddCount 3622 13 = 8 ∧ acceleratedOrbit 13 3622 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3622 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3622) = 3 ^ 8 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3622.1, data_13_3622.2]

/-- Complete interval computation for depth 13, residue 3623. -/
theorem bounds_13_3623 : exactInterval 13 3623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3623 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3623) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3623 : oddCount 3623 13 = 6 ∧ acceleratedOrbit 13 3623 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3623 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3623) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3623.1, data_13_3623.2]

/-- Complete interval computation for depth 13, residue 3624. -/
theorem bounds_13_3624 : exactInterval 13 3624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3624 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3624) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3624 : oddCount 3624 13 = 2 ∧ acceleratedOrbit 13 3624 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3624 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3624) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3624.1, data_13_3624.2]

/-- Complete interval computation for depth 13, residue 3625. -/
theorem bounds_13_3625 : exactInterval 13 3625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3625 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3625) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3625 : oddCount 3625 13 = 9 ∧ acceleratedOrbit 13 3625 = 8714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3625 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3625) = 3 ^ 9 * m + 8714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3625.1, data_13_3625.2]

/-- Complete interval computation for depth 13, residue 3626. -/
theorem bounds_13_3626 : exactInterval 13 3626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3626 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3626) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3626 : oddCount 3626 13 = 2 ∧ acceleratedOrbit 13 3626 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3626 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3626) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3626.1, data_13_3626.2]

/-- Complete interval computation for depth 13, residue 3627. -/
theorem bounds_13_3627 : exactInterval 13 3627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3627 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3627) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3627 : oddCount 3627 13 = 7 ∧ acceleratedOrbit 13 3627 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3627 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3627) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3627.1, data_13_3627.2]

/-- Complete interval computation for depth 13, residue 3628. -/
theorem bounds_13_3628 : exactInterval 13 3628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3628 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3628) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3628 : oddCount 3628 13 = 8 ∧ acceleratedOrbit 13 3628 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3628 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3628) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3628.1, data_13_3628.2]

/-- Complete interval computation for depth 13, residue 3629. -/
theorem bounds_13_3629 : exactInterval 13 3629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3629 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3629) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3629 : oddCount 3629 13 = 8 ∧ acceleratedOrbit 13 3629 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3629 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3629) = 3 ^ 8 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3629.1, data_13_3629.2]

end Collatz.Research.StoppingAtlas.Batch0703
