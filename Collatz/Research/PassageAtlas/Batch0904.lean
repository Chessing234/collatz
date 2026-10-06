import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0904

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29589. -/
theorem bounds_15_29589 : exactInterval 15 29589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29589 : oddCount 29589 15 = 6 ∧ acceleratedOrbit 15 29589 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29589) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29589.1, data_15_29589.2]

/-- Complete interval computation for depth 15, residue 29590. -/
theorem bounds_15_29590 : exactInterval 15 29590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29590 : oddCount 29590 15 = 6 ∧ acceleratedOrbit 15 29590 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29590) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29590.1, data_15_29590.2]

/-- Complete interval computation for depth 15, residue 29591. -/
theorem bounds_15_29591 : exactInterval 15 29591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29591 : oddCount 29591 15 = 6 ∧ acceleratedOrbit 15 29591 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29591) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29591.1, data_15_29591.2]

/-- Complete interval computation for depth 15, residue 29592. -/
theorem bounds_15_29592 : exactInterval 15 29592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29592 : oddCount 29592 15 = 6 ∧ acceleratedOrbit 15 29592 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29592) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29592.1, data_15_29592.2]

/-- Complete interval computation for depth 15, residue 29593. -/
theorem bounds_15_29593 : exactInterval 15 29593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29593 : oddCount 29593 15 = 6 ∧ acceleratedOrbit 15 29593 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29593) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29593.1, data_15_29593.2]

/-- Complete interval computation for depth 15, residue 29594. -/
theorem bounds_15_29594 : exactInterval 15 29594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29594 : oddCount 29594 15 = 6 ∧ acceleratedOrbit 15 29594 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29594) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29594.1, data_15_29594.2]

/-- Complete interval computation for depth 15, residue 29595. -/
theorem bounds_15_29595 : exactInterval 15 29595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29595 : oddCount 29595 15 = 9 ∧ acceleratedOrbit 15 29595 = 17779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29595) = 3 ^ 9 * m + 17779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29595.1, data_15_29595.2]

/-- Complete interval computation for depth 15, residue 29596. -/
theorem bounds_15_29596 : exactInterval 15 29596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29596 : oddCount 29596 15 = 8 ∧ acceleratedOrbit 15 29596 = 5927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29596) = 3 ^ 8 * m + 5927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29596.1, data_15_29596.2]

/-- Complete interval computation for depth 15, residue 29597. -/
theorem bounds_15_29597 : exactInterval 15 29597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29597 : oddCount 29597 15 = 8 ∧ acceleratedOrbit 15 29597 = 5927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29597) = 3 ^ 8 * m + 5927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29597.1, data_15_29597.2]

/-- Complete interval computation for depth 15, residue 29598. -/
theorem bounds_15_29598 : exactInterval 15 29598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29598 : oddCount 29598 15 = 8 ∧ acceleratedOrbit 15 29598 = 5927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29598) = 3 ^ 8 * m + 5927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29598.1, data_15_29598.2]

/-- Complete interval computation for depth 15, residue 29599. -/
theorem bounds_15_29599 : exactInterval 15 29599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29599 : oddCount 29599 15 = 10 ∧ acceleratedOrbit 15 29599 = 53342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29599) = 3 ^ 10 * m + 53342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29599.1, data_15_29599.2]

/-- Complete interval computation for depth 15, residue 29600. -/
theorem bounds_15_29600 : exactInterval 15 29600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29600 : oddCount 29600 15 = 6 ∧ acceleratedOrbit 15 29600 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29600) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29600.1, data_15_29600.2]

/-- Complete interval computation for depth 15, residue 29601. -/
theorem bounds_15_29601 : exactInterval 15 29601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29601 : oddCount 29601 15 = 7 ∧ acceleratedOrbit 15 29601 = 1976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29601) = 3 ^ 7 * m + 1976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29601.1, data_15_29601.2]

/-- Complete interval computation for depth 15, residue 29602. -/
theorem bounds_15_29602 : exactInterval 15 29602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29602 : oddCount 29602 15 = 6 ∧ acceleratedOrbit 15 29602 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29602) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29602.1, data_15_29602.2]

/-- Complete interval computation for depth 15, residue 29603. -/
theorem bounds_15_29603 : exactInterval 15 29603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29603 : oddCount 29603 15 = 6 ∧ acceleratedOrbit 15 29603 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29603) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29603.1, data_15_29603.2]

/-- Complete interval computation for depth 15, residue 29604. -/
theorem bounds_15_29604 : exactInterval 15 29604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29604 : oddCount 29604 15 = 8 ∧ acceleratedOrbit 15 29604 = 5930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29604) = 3 ^ 8 * m + 5930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29604.1, data_15_29604.2]

/-- Complete interval computation for depth 15, residue 29605. -/
theorem bounds_15_29605 : exactInterval 15 29605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29605 : oddCount 29605 15 = 8 ∧ acceleratedOrbit 15 29605 = 5930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29605) = 3 ^ 8 * m + 5930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29605.1, data_15_29605.2]

/-- Complete interval computation for depth 15, residue 29606. -/
theorem bounds_15_29606 : exactInterval 15 29606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29606 : oddCount 29606 15 = 8 ∧ acceleratedOrbit 15 29606 = 5930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29606) = 3 ^ 8 * m + 5930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29606.1, data_15_29606.2]

/-- Complete interval computation for depth 15, residue 29607. -/
theorem bounds_15_29607 : exactInterval 15 29607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29607 : oddCount 29607 15 = 9 ∧ acceleratedOrbit 15 29607 = 17786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29607) = 3 ^ 9 * m + 17786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29607.1, data_15_29607.2]

/-- Complete interval computation for depth 15, residue 29608. -/
theorem bounds_15_29608 : exactInterval 15 29608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29608 : oddCount 29608 15 = 6 ∧ acceleratedOrbit 15 29608 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29608) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29608.1, data_15_29608.2]

/-- Complete interval computation for depth 15, residue 29609. -/
theorem bounds_15_29609 : exactInterval 15 29609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29609 : oddCount 29609 15 = 10 ∧ acceleratedOrbit 15 29609 = 53360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29609) = 3 ^ 10 * m + 53360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29609.1, data_15_29609.2]

/-- Complete interval computation for depth 15, residue 29610. -/
theorem bounds_15_29610 : exactInterval 15 29610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29610 : oddCount 29610 15 = 6 ∧ acceleratedOrbit 15 29610 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29610) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29610.1, data_15_29610.2]

/-- Complete interval computation for depth 15, residue 29611. -/
theorem bounds_15_29611 : exactInterval 15 29611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29611 : oddCount 29611 15 = 8 ∧ acceleratedOrbit 15 29611 = 5930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29611) = 3 ^ 8 * m + 5930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29611.1, data_15_29611.2]

/-- Complete interval computation for depth 15, residue 29612. -/
theorem bounds_15_29612 : exactInterval 15 29612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29612 : oddCount 29612 15 = 10 ∧ acceleratedOrbit 15 29612 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29612) = 3 ^ 10 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29612.1, data_15_29612.2]

/-- Complete interval computation for depth 15, residue 29613. -/
theorem bounds_15_29613 : exactInterval 15 29613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29613 : oddCount 29613 15 = 10 ∧ acceleratedOrbit 15 29613 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29613) = 3 ^ 10 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29613.1, data_15_29613.2]

/-- Complete interval computation for depth 15, residue 29614. -/
theorem bounds_15_29614 : exactInterval 15 29614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29614 : oddCount 29614 15 = 10 ∧ acceleratedOrbit 15 29614 = 53378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29614) = 3 ^ 10 * m + 53378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29614.1, data_15_29614.2]

/-- Complete interval computation for depth 15, residue 29615. -/
theorem bounds_15_29615 : exactInterval 15 29615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29615 : oddCount 29615 15 = 6 ∧ acceleratedOrbit 15 29615 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29615) = 3 ^ 6 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29615.1, data_15_29615.2]

/-- Complete interval computation for depth 15, residue 29616. -/
theorem bounds_15_29616 : exactInterval 15 29616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29616 : oddCount 29616 15 = 5 ∧ acceleratedOrbit 15 29616 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29616) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29616.1, data_15_29616.2]

/-- Complete interval computation for depth 15, residue 29617. -/
theorem bounds_15_29617 : exactInterval 15 29617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29617 : oddCount 29617 15 = 5 ∧ acceleratedOrbit 15 29617 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29617) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29617.1, data_15_29617.2]

/-- Complete interval computation for depth 15, residue 29618. -/
theorem bounds_15_29618 : exactInterval 15 29618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29618 : oddCount 29618 15 = 5 ∧ acceleratedOrbit 15 29618 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29618) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29618.1, data_15_29618.2]

/-- Complete interval computation for depth 15, residue 29619. -/
theorem bounds_15_29619 : exactInterval 15 29619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29619 : oddCount 29619 15 = 5 ∧ acceleratedOrbit 15 29619 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29619) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29619.1, data_15_29619.2]

/-- Complete interval computation for depth 15, residue 29620. -/
theorem bounds_15_29620 : exactInterval 15 29620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29620 : oddCount 29620 15 = 5 ∧ acceleratedOrbit 15 29620 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29620) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29620.1, data_15_29620.2]

/-- Complete interval computation for depth 15, residue 29621. -/
theorem bounds_15_29621 : exactInterval 15 29621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29621 : oddCount 29621 15 = 5 ∧ acceleratedOrbit 15 29621 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29621) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29621.1, data_15_29621.2]

end Collatz.Research.PassageAtlas.Batch0904
