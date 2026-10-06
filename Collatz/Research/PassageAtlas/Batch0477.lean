import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0477

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15597. -/
theorem bounds_15_15597 : exactInterval 15 15597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15597 : oddCount 15597 15 = 7 ∧ acceleratedOrbit 15 15597 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15597) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15597.1, data_15_15597.2]

/-- Complete interval computation for depth 15, residue 15598. -/
theorem bounds_15_15598 : exactInterval 15 15598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15598 : oddCount 15598 15 = 7 ∧ acceleratedOrbit 15 15598 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15598) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15598.1, data_15_15598.2]

/-- Complete interval computation for depth 15, residue 15599. -/
theorem bounds_15_15599 : exactInterval 15 15599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15599 : oddCount 15599 15 = 10 ∧ acceleratedOrbit 15 15599 = 28112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15599) = 3 ^ 10 * m + 28112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15599.1, data_15_15599.2]

/-- Complete interval computation for depth 15, residue 15600. -/
theorem bounds_15_15600 : exactInterval 15 15600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15600 : oddCount 15600 15 = 7 ∧ acceleratedOrbit 15 15600 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15600) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15600.1, data_15_15600.2]

/-- Complete interval computation for depth 15, residue 15601. -/
theorem bounds_15_15601 : exactInterval 15 15601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15601 : oddCount 15601 15 = 7 ∧ acceleratedOrbit 15 15601 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15601) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15601.1, data_15_15601.2]

/-- Complete interval computation for depth 15, residue 15602. -/
theorem bounds_15_15602 : exactInterval 15 15602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15602 : oddCount 15602 15 = 8 ∧ acceleratedOrbit 15 15602 = 3125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15602) = 3 ^ 8 * m + 3125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15602.1, data_15_15602.2]

/-- Complete interval computation for depth 15, residue 15603. -/
theorem bounds_15_15603 : exactInterval 15 15603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15603 : oddCount 15603 15 = 8 ∧ acceleratedOrbit 15 15603 = 3125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15603) = 3 ^ 8 * m + 3125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15603.1, data_15_15603.2]

/-- Complete interval computation for depth 15, residue 15604. -/
theorem bounds_15_15604 : exactInterval 15 15604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15604 : oddCount 15604 15 = 7 ∧ acceleratedOrbit 15 15604 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15604) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15604.1, data_15_15604.2]

/-- Complete interval computation for depth 15, residue 15605. -/
theorem bounds_15_15605 : exactInterval 15 15605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15605 : oddCount 15605 15 = 7 ∧ acceleratedOrbit 15 15605 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15605) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15605.1, data_15_15605.2]

/-- Complete interval computation for depth 15, residue 15606. -/
theorem bounds_15_15606 : exactInterval 15 15606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15606 : oddCount 15606 15 = 7 ∧ acceleratedOrbit 15 15606 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15606) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15606.1, data_15_15606.2]

/-- Complete interval computation for depth 15, residue 15607. -/
theorem bounds_15_15607 : exactInterval 15 15607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15607 : oddCount 15607 15 = 7 ∧ acceleratedOrbit 15 15607 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15607) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15607.1, data_15_15607.2]

/-- Complete interval computation for depth 15, residue 15608. -/
theorem bounds_15_15608 : exactInterval 15 15608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15608 : oddCount 15608 15 = 8 ∧ acceleratedOrbit 15 15608 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15608) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15608.1, data_15_15608.2]

/-- Complete interval computation for depth 15, residue 15609. -/
theorem bounds_15_15609 : exactInterval 15 15609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15609 : oddCount 15609 15 = 7 ∧ acceleratedOrbit 15 15609 = 1042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15609) = 3 ^ 7 * m + 1042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15609.1, data_15_15609.2]

/-- Complete interval computation for depth 15, residue 15610. -/
theorem bounds_15_15610 : exactInterval 15 15610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15610 : oddCount 15610 15 = 8 ∧ acceleratedOrbit 15 15610 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15610) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15610.1, data_15_15610.2]

/-- Complete interval computation for depth 15, residue 15611. -/
theorem bounds_15_15611 : exactInterval 15 15611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15611 : oddCount 15611 15 = 10 ∧ acceleratedOrbit 15 15611 = 28135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15611) = 3 ^ 10 * m + 28135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15611.1, data_15_15611.2]

/-- Complete interval computation for depth 15, residue 15612. -/
theorem bounds_15_15612 : exactInterval 15 15612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15612 : oddCount 15612 15 = 8 ∧ acceleratedOrbit 15 15612 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15612) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15612.1, data_15_15612.2]

/-- Complete interval computation for depth 15, residue 15613. -/
theorem bounds_15_15613 : exactInterval 15 15613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15613 : oddCount 15613 15 = 8 ∧ acceleratedOrbit 15 15613 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15613) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15613.1, data_15_15613.2]

/-- Complete interval computation for depth 15, residue 15614. -/
theorem bounds_15_15614 : exactInterval 15 15614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15614 : oddCount 15614 15 = 11 ∧ acceleratedOrbit 15 15614 = 84422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15614) = 3 ^ 11 * m + 84422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15614.1, data_15_15614.2]

/-- Complete interval computation for depth 15, residue 15615. -/
theorem bounds_15_15615 : exactInterval 15 15615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15615 : oddCount 15615 15 = 11 ∧ acceleratedOrbit 15 15615 = 84422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15615) = 3 ^ 11 * m + 84422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15615.1, data_15_15615.2]

/-- Complete interval computation for depth 15, residue 15616. -/
theorem bounds_15_15616 : exactInterval 15 15616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15616 : oddCount 15616 15 = 4 ∧ acceleratedOrbit 15 15616 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15616) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15616.1, data_15_15616.2]

/-- Complete interval computation for depth 15, residue 15617. -/
theorem bounds_15_15617 : exactInterval 15 15617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15617 : oddCount 15617 15 = 9 ∧ acceleratedOrbit 15 15617 = 9386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15617) = 3 ^ 9 * m + 9386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15617.1, data_15_15617.2]

/-- Complete interval computation for depth 15, residue 15618. -/
theorem bounds_15_15618 : exactInterval 15 15618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15618 : oddCount 15618 15 = 9 ∧ acceleratedOrbit 15 15618 = 9386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15618) = 3 ^ 9 * m + 9386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15618.1, data_15_15618.2]

/-- Complete interval computation for depth 15, residue 15619. -/
theorem bounds_15_15619 : exactInterval 15 15619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15619 : oddCount 15619 15 = 9 ∧ acceleratedOrbit 15 15619 = 9386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15619) = 3 ^ 9 * m + 9386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15619.1, data_15_15619.2]

/-- Complete interval computation for depth 15, residue 15620. -/
theorem bounds_15_15620 : exactInterval 15 15620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15620 : oddCount 15620 15 = 6 ∧ acceleratedOrbit 15 15620 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15620) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15620.1, data_15_15620.2]

/-- Complete interval computation for depth 15, residue 15621. -/
theorem bounds_15_15621 : exactInterval 15 15621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15621 : oddCount 15621 15 = 6 ∧ acceleratedOrbit 15 15621 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15621) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15621.1, data_15_15621.2]

/-- Complete interval computation for depth 15, residue 15622. -/
theorem bounds_15_15622 : exactInterval 15 15622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15622 : oddCount 15622 15 = 6 ∧ acceleratedOrbit 15 15622 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15622) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15622.1, data_15_15622.2]

/-- Complete interval computation for depth 15, residue 15623. -/
theorem bounds_15_15623 : exactInterval 15 15623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15623 : oddCount 15623 15 = 11 ∧ acceleratedOrbit 15 15623 = 84473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15623) = 3 ^ 11 * m + 84473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15623.1, data_15_15623.2]

/-- Complete interval computation for depth 15, residue 15624. -/
theorem bounds_15_15624 : exactInterval 15 15624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15624 : oddCount 15624 15 = 5 ∧ acceleratedOrbit 15 15624 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15624) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15624.1, data_15_15624.2]

/-- Complete interval computation for depth 15, residue 15625. -/
theorem bounds_15_15625 : exactInterval 15 15625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15625 : oddCount 15625 15 = 7 ∧ acceleratedOrbit 15 15625 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15625) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15625.1, data_15_15625.2]

/-- Complete interval computation for depth 15, residue 15626. -/
theorem bounds_15_15626 : exactInterval 15 15626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15626 : oddCount 15626 15 = 5 ∧ acceleratedOrbit 15 15626 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15626) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15626.1, data_15_15626.2]

/-- Complete interval computation for depth 15, residue 15627. -/
theorem bounds_15_15627 : exactInterval 15 15627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15627 : oddCount 15627 15 = 8 ∧ acceleratedOrbit 15 15627 = 3131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15627) = 3 ^ 8 * m + 3131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15627.1, data_15_15627.2]

/-- Complete interval computation for depth 15, residue 15628. -/
theorem bounds_15_15628 : exactInterval 15 15628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15628 : oddCount 15628 15 = 5 ∧ acceleratedOrbit 15 15628 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15628) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15628.1, data_15_15628.2]

/-- Complete interval computation for depth 15, residue 15629. -/
theorem bounds_15_15629 : exactInterval 15 15629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15629 : oddCount 15629 15 = 5 ∧ acceleratedOrbit 15 15629 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15629) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15629.1, data_15_15629.2]

end Collatz.Research.PassageAtlas.Batch0477
