import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0905

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29622. -/
theorem bounds_15_29622 : exactInterval 15 29622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29622 : oddCount 29622 15 = 8 ∧ acceleratedOrbit 15 29622 = 5933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29622) = 3 ^ 8 * m + 5933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29622.1, data_15_29622.2]

/-- Complete interval computation for depth 15, residue 29623. -/
theorem bounds_15_29623 : exactInterval 15 29623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29623 : oddCount 29623 15 = 8 ∧ acceleratedOrbit 15 29623 = 5933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29623) = 3 ^ 8 * m + 5933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29623.1, data_15_29623.2]

/-- Complete interval computation for depth 15, residue 29624. -/
theorem bounds_15_29624 : exactInterval 15 29624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29624 : oddCount 29624 15 = 5 ∧ acceleratedOrbit 15 29624 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29624) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29624.1, data_15_29624.2]

/-- Complete interval computation for depth 15, residue 29625. -/
theorem bounds_15_29625 : exactInterval 15 29625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29625 : oddCount 29625 15 = 8 ∧ acceleratedOrbit 15 29625 = 5933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29625) = 3 ^ 8 * m + 5933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29625.1, data_15_29625.2]

/-- Complete interval computation for depth 15, residue 29626. -/
theorem bounds_15_29626 : exactInterval 15 29626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29626 : oddCount 29626 15 = 5 ∧ acceleratedOrbit 15 29626 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29626) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29626.1, data_15_29626.2]

/-- Complete interval computation for depth 15, residue 29627. -/
theorem bounds_15_29627 : exactInterval 15 29627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29627 : oddCount 29627 15 = 8 ∧ acceleratedOrbit 15 29627 = 5933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29627) = 3 ^ 8 * m + 5933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29627.1, data_15_29627.2]

/-- Complete interval computation for depth 15, residue 29628. -/
theorem bounds_15_29628 : exactInterval 15 29628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29628 : oddCount 29628 15 = 10 ∧ acceleratedOrbit 15 29628 = 53399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29628) = 3 ^ 10 * m + 53399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29628.1, data_15_29628.2]

/-- Complete interval computation for depth 15, residue 29629. -/
theorem bounds_15_29629 : exactInterval 15 29629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29629 : oddCount 29629 15 = 10 ∧ acceleratedOrbit 15 29629 = 53399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29629) = 3 ^ 10 * m + 53399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29629.1, data_15_29629.2]

/-- Complete interval computation for depth 15, residue 29630. -/
theorem bounds_15_29630 : exactInterval 15 29630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29630 : oddCount 29630 15 = 10 ∧ acceleratedOrbit 15 29630 = 53399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29630) = 3 ^ 10 * m + 53399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29630.1, data_15_29630.2]

/-- Complete interval computation for depth 15, residue 29631. -/
theorem bounds_15_29631 : exactInterval 15 29631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29631 : oddCount 29631 15 = 10 ∧ acceleratedOrbit 15 29631 = 53398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29631) = 3 ^ 10 * m + 53398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29631.1, data_15_29631.2]

/-- Complete interval computation for depth 15, residue 29632. -/
theorem bounds_15_29632 : exactInterval 15 29632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29632 : oddCount 29632 15 = 6 ∧ acceleratedOrbit 15 29632 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29632) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29632.1, data_15_29632.2]

/-- Complete interval computation for depth 15, residue 29633. -/
theorem bounds_15_29633 : exactInterval 15 29633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29633 : oddCount 29633 15 = 8 ∧ acceleratedOrbit 15 29633 = 5935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29633) = 3 ^ 8 * m + 5935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29633.1, data_15_29633.2]

/-- Complete interval computation for depth 15, residue 29634. -/
theorem bounds_15_29634 : exactInterval 15 29634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29634 : oddCount 29634 15 = 8 ∧ acceleratedOrbit 15 29634 = 5935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29634) = 3 ^ 8 * m + 5935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29634.1, data_15_29634.2]

/-- Complete interval computation for depth 15, residue 29635. -/
theorem bounds_15_29635 : exactInterval 15 29635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29635 : oddCount 29635 15 = 8 ∧ acceleratedOrbit 15 29635 = 5935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29635) = 3 ^ 8 * m + 5935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29635.1, data_15_29635.2]

/-- Complete interval computation for depth 15, residue 29636. -/
theorem bounds_15_29636 : exactInterval 15 29636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29636 : oddCount 29636 15 = 6 ∧ acceleratedOrbit 15 29636 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29636) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29636.1, data_15_29636.2]

/-- Complete interval computation for depth 15, residue 29637. -/
theorem bounds_15_29637 : exactInterval 15 29637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29637 : oddCount 29637 15 = 6 ∧ acceleratedOrbit 15 29637 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29637) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29637.1, data_15_29637.2]

/-- Complete interval computation for depth 15, residue 29638. -/
theorem bounds_15_29638 : exactInterval 15 29638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29638 : oddCount 29638 15 = 6 ∧ acceleratedOrbit 15 29638 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29638) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29638.1, data_15_29638.2]

/-- Complete interval computation for depth 15, residue 29639. -/
theorem bounds_15_29639 : exactInterval 15 29639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29639 : oddCount 29639 15 = 11 ∧ acceleratedOrbit 15 29639 = 160244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29639) = 3 ^ 11 * m + 160244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29639.1, data_15_29639.2]

/-- Complete interval computation for depth 15, residue 29640. -/
theorem bounds_15_29640 : exactInterval 15 29640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29640 : oddCount 29640 15 = 8 ∧ acceleratedOrbit 15 29640 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29640) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29640.1, data_15_29640.2]

/-- Complete interval computation for depth 15, residue 29641. -/
theorem bounds_15_29641 : exactInterval 15 29641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29641 : oddCount 29641 15 = 7 ∧ acceleratedOrbit 15 29641 = 1979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29641) = 3 ^ 7 * m + 1979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29641.1, data_15_29641.2]

/-- Complete interval computation for depth 15, residue 29642. -/
theorem bounds_15_29642 : exactInterval 15 29642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29642 : oddCount 29642 15 = 8 ∧ acceleratedOrbit 15 29642 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29642) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29642.1, data_15_29642.2]

/-- Complete interval computation for depth 15, residue 29643. -/
theorem bounds_15_29643 : exactInterval 15 29643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29643 : oddCount 29643 15 = 8 ∧ acceleratedOrbit 15 29643 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29643) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29643.1, data_15_29643.2]

/-- Complete interval computation for depth 15, residue 29644. -/
theorem bounds_15_29644 : exactInterval 15 29644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29644 : oddCount 29644 15 = 8 ∧ acceleratedOrbit 15 29644 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29644) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29644.1, data_15_29644.2]

/-- Complete interval computation for depth 15, residue 29645. -/
theorem bounds_15_29645 : exactInterval 15 29645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29645 : oddCount 29645 15 = 8 ∧ acceleratedOrbit 15 29645 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29645) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29645.1, data_15_29645.2]

/-- Complete interval computation for depth 15, residue 29646. -/
theorem bounds_15_29646 : exactInterval 15 29646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29646 : oddCount 29646 15 = 9 ∧ acceleratedOrbit 15 29646 = 17810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29646) = 3 ^ 9 * m + 17810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29646.1, data_15_29646.2]

/-- Complete interval computation for depth 15, residue 29647. -/
theorem bounds_15_29647 : exactInterval 15 29647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29647 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29647) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29647 : oddCount 29647 15 = 9 ∧ acceleratedOrbit 15 29647 = 17810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29647 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29647) = 3 ^ 9 * m + 17810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29647.1, data_15_29647.2]

/-- Complete interval computation for depth 15, residue 29648. -/
theorem bounds_15_29648 : exactInterval 15 29648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29648 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29648) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29648 : oddCount 29648 15 = 6 ∧ acceleratedOrbit 15 29648 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29648 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29648) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29648.1, data_15_29648.2]

/-- Complete interval computation for depth 15, residue 29649. -/
theorem bounds_15_29649 : exactInterval 15 29649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29649 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29649) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29649 : oddCount 29649 15 = 8 ∧ acceleratedOrbit 15 29649 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29649 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29649) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29649.1, data_15_29649.2]

/-- Complete interval computation for depth 15, residue 29650. -/
theorem bounds_15_29650 : exactInterval 15 29650 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29650 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29650) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29650 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29650 : oddCount 29650 15 = 9 ∧ acceleratedOrbit 15 29650 = 17813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29650 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29650) = 3 ^ 9 * m + 17813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29650.1, data_15_29650.2]

/-- Complete interval computation for depth 15, residue 29651. -/
theorem bounds_15_29651 : exactInterval 15 29651 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29651 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29651) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29651 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29651 : oddCount 29651 15 = 9 ∧ acceleratedOrbit 15 29651 = 17813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29651 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29651) = 3 ^ 9 * m + 17813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29651.1, data_15_29651.2]

/-- Complete interval computation for depth 15, residue 29652. -/
theorem bounds_15_29652 : exactInterval 15 29652 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29652 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29652) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29652 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29652 : oddCount 29652 15 = 6 ∧ acceleratedOrbit 15 29652 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29652 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29652) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29652.1, data_15_29652.2]

/-- Complete interval computation for depth 15, residue 29653. -/
theorem bounds_15_29653 : exactInterval 15 29653 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29653 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29653) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29653 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29653 : oddCount 29653 15 = 6 ∧ acceleratedOrbit 15 29653 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29653 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29653) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29653.1, data_15_29653.2]

/-- Complete interval computation for depth 15, residue 29654. -/
theorem bounds_15_29654 : exactInterval 15 29654 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29654 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29654) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29654 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29654 : oddCount 29654 15 = 9 ∧ acceleratedOrbit 15 29654 = 17815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29654 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29654) = 3 ^ 9 * m + 17815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29654.1, data_15_29654.2]

end Collatz.Research.PassageAtlas.Batch0905
