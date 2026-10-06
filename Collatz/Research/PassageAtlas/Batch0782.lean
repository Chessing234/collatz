import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0782

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25591. -/
theorem bounds_15_25591 : exactInterval 15 25591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25591 : oddCount 25591 15 = 8 ∧ acceleratedOrbit 15 25591 = 5125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25591) = 3 ^ 8 * m + 5125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25591.1, data_15_25591.2]

/-- Complete interval computation for depth 15, residue 25592. -/
theorem bounds_15_25592 : exactInterval 15 25592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25592 : oddCount 25592 15 = 10 ∧ acceleratedOrbit 15 25592 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25592) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25592.1, data_15_25592.2]

/-- Complete interval computation for depth 15, residue 25593. -/
theorem bounds_15_25593 : exactInterval 15 25593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25593 : oddCount 25593 15 = 11 ∧ acceleratedOrbit 15 25593 = 138374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25593) = 3 ^ 11 * m + 138374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25593.1, data_15_25593.2]

/-- Complete interval computation for depth 15, residue 25594. -/
theorem bounds_15_25594 : exactInterval 15 25594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25594 : oddCount 25594 15 = 10 ∧ acceleratedOrbit 15 25594 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25594) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25594.1, data_15_25594.2]

/-- Complete interval computation for depth 15, residue 25595. -/
theorem bounds_15_25595 : exactInterval 15 25595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25595 : oddCount 25595 15 = 9 ∧ acceleratedOrbit 15 25595 = 15376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25595) = 3 ^ 9 * m + 15376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25595.1, data_15_25595.2]

/-- Complete interval computation for depth 15, residue 25596. -/
theorem bounds_15_25596 : exactInterval 15 25596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25596 : oddCount 25596 15 = 10 ∧ acceleratedOrbit 15 25596 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25596) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25596.1, data_15_25596.2]

/-- Complete interval computation for depth 15, residue 25597. -/
theorem bounds_15_25597 : exactInterval 15 25597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25597 : oddCount 25597 15 = 10 ∧ acceleratedOrbit 15 25597 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25597) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25597.1, data_15_25597.2]

/-- Complete interval computation for depth 15, residue 25598. -/
theorem bounds_15_25598 : exactInterval 15 25598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25598 : oddCount 25598 15 = 10 ∧ acceleratedOrbit 15 25598 = 46132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25598) = 3 ^ 10 * m + 46132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25598.1, data_15_25598.2]

/-- Complete interval computation for depth 15, residue 25599. -/
theorem bounds_15_25599 : exactInterval 15 25599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25599 : oddCount 25599 15 = 10 ∧ acceleratedOrbit 15 25599 = 46132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25599) = 3 ^ 10 * m + 46132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25599.1, data_15_25599.2]

/-- Complete interval computation for depth 15, residue 25600. -/
theorem bounds_15_25600 : exactInterval 15 25600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25600 : oddCount 25600 15 = 3 ∧ acceleratedOrbit 15 25600 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25600) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25600.1, data_15_25600.2]

/-- Complete interval computation for depth 15, residue 25601. -/
theorem bounds_15_25601 : exactInterval 15 25601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25601 : oddCount 25601 15 = 8 ∧ acceleratedOrbit 15 25601 = 5129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25601) = 3 ^ 8 * m + 5129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25601.1, data_15_25601.2]

/-- Complete interval computation for depth 15, residue 25602. -/
theorem bounds_15_25602 : exactInterval 15 25602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25602 : oddCount 25602 15 = 8 ∧ acceleratedOrbit 15 25602 = 5129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25602) = 3 ^ 8 * m + 5129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25602.1, data_15_25602.2]

/-- Complete interval computation for depth 15, residue 25603. -/
theorem bounds_15_25603 : exactInterval 15 25603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25603 : oddCount 25603 15 = 8 ∧ acceleratedOrbit 15 25603 = 5129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25603) = 3 ^ 8 * m + 5129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25603.1, data_15_25603.2]

/-- Complete interval computation for depth 15, residue 25604. -/
theorem bounds_15_25604 : exactInterval 15 25604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25604 : oddCount 25604 15 = 5 ∧ acceleratedOrbit 15 25604 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25604) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25604.1, data_15_25604.2]

/-- Complete interval computation for depth 15, residue 25605. -/
theorem bounds_15_25605 : exactInterval 15 25605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25605 : oddCount 25605 15 = 5 ∧ acceleratedOrbit 15 25605 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25605) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25605.1, data_15_25605.2]

/-- Complete interval computation for depth 15, residue 25606. -/
theorem bounds_15_25606 : exactInterval 15 25606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25606 : oddCount 25606 15 = 5 ∧ acceleratedOrbit 15 25606 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25606) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25606.1, data_15_25606.2]

/-- Complete interval computation for depth 15, residue 25607. -/
theorem bounds_15_25607 : exactInterval 15 25607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25607 : oddCount 25607 15 = 8 ∧ acceleratedOrbit 15 25607 = 5129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25607) = 3 ^ 8 * m + 5129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25607.1, data_15_25607.2]

/-- Complete interval computation for depth 15, residue 25608. -/
theorem bounds_15_25608 : exactInterval 15 25608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25608 : oddCount 25608 15 = 7 ∧ acceleratedOrbit 15 25608 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25608) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25608.1, data_15_25608.2]

/-- Complete interval computation for depth 15, residue 25609. -/
theorem bounds_15_25609 : exactInterval 15 25609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25609 : oddCount 25609 15 = 9 ∧ acceleratedOrbit 15 25609 = 15385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25609) = 3 ^ 9 * m + 15385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25609.1, data_15_25609.2]

/-- Complete interval computation for depth 15, residue 25610. -/
theorem bounds_15_25610 : exactInterval 15 25610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25610 : oddCount 25610 15 = 7 ∧ acceleratedOrbit 15 25610 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25610) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25610.1, data_15_25610.2]

/-- Complete interval computation for depth 15, residue 25611. -/
theorem bounds_15_25611 : exactInterval 15 25611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25611 : oddCount 25611 15 = 5 ∧ acceleratedOrbit 15 25611 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25611) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25611.1, data_15_25611.2]

/-- Complete interval computation for depth 15, residue 25612. -/
theorem bounds_15_25612 : exactInterval 15 25612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25612 : oddCount 25612 15 = 7 ∧ acceleratedOrbit 15 25612 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25612) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25612.1, data_15_25612.2]

/-- Complete interval computation for depth 15, residue 25613. -/
theorem bounds_15_25613 : exactInterval 15 25613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25613 : oddCount 25613 15 = 7 ∧ acceleratedOrbit 15 25613 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25613) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25613.1, data_15_25613.2]

/-- Complete interval computation for depth 15, residue 25614. -/
theorem bounds_15_25614 : exactInterval 15 25614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25614 : oddCount 25614 15 = 10 ∧ acceleratedOrbit 15 25614 = 46169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25614) = 3 ^ 10 * m + 46169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25614.1, data_15_25614.2]

/-- Complete interval computation for depth 15, residue 25615. -/
theorem bounds_15_25615 : exactInterval 15 25615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25615 : oddCount 25615 15 = 10 ∧ acceleratedOrbit 15 25615 = 46169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25615) = 3 ^ 10 * m + 46169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25615.1, data_15_25615.2]

/-- Complete interval computation for depth 15, residue 25616. -/
theorem bounds_15_25616 : exactInterval 15 25616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25616 : oddCount 25616 15 = 5 ∧ acceleratedOrbit 15 25616 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25616) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25616.1, data_15_25616.2]

/-- Complete interval computation for depth 15, residue 25617. -/
theorem bounds_15_25617 : exactInterval 15 25617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25617 : oddCount 25617 15 = 7 ∧ acceleratedOrbit 15 25617 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25617) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25617.1, data_15_25617.2]

/-- Complete interval computation for depth 15, residue 25618. -/
theorem bounds_15_25618 : exactInterval 15 25618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25618 : oddCount 25618 15 = 5 ∧ acceleratedOrbit 15 25618 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25618) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25618.1, data_15_25618.2]

/-- Complete interval computation for depth 15, residue 25619. -/
theorem bounds_15_25619 : exactInterval 15 25619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25619 : oddCount 25619 15 = 5 ∧ acceleratedOrbit 15 25619 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25619) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25619.1, data_15_25619.2]

/-- Complete interval computation for depth 15, residue 25620. -/
theorem bounds_15_25620 : exactInterval 15 25620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25620 : oddCount 25620 15 = 5 ∧ acceleratedOrbit 15 25620 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25620) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25620.1, data_15_25620.2]

/-- Complete interval computation for depth 15, residue 25621. -/
theorem bounds_15_25621 : exactInterval 15 25621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25621 : oddCount 25621 15 = 5 ∧ acceleratedOrbit 15 25621 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25621) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25621.1, data_15_25621.2]

/-- Complete interval computation for depth 15, residue 25622. -/
theorem bounds_15_25622 : exactInterval 15 25622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25622 : oddCount 25622 15 = 7 ∧ acceleratedOrbit 15 25622 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25622) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25622.1, data_15_25622.2]

/-- Complete interval computation for depth 15, residue 25623. -/
theorem bounds_15_25623 : exactInterval 15 25623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25623 : oddCount 25623 15 = 7 ∧ acceleratedOrbit 15 25623 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25623) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25623.1, data_15_25623.2]

end Collatz.Research.PassageAtlas.Batch0782
