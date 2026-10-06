import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0691

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22609. -/
theorem bounds_15_22609 : exactInterval 15 22609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22609 : oddCount 22609 15 = 8 ∧ acceleratedOrbit 15 22609 = 4529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22609) = 3 ^ 8 * m + 4529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22609.1, data_15_22609.2]

/-- Complete interval computation for depth 15, residue 22610. -/
theorem bounds_15_22610 : exactInterval 15 22610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22610 : oddCount 22610 15 = 8 ∧ acceleratedOrbit 15 22610 = 4528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22610) = 3 ^ 8 * m + 4528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22610.1, data_15_22610.2]

/-- Complete interval computation for depth 15, residue 22611. -/
theorem bounds_15_22611 : exactInterval 15 22611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22611 : oddCount 22611 15 = 8 ∧ acceleratedOrbit 15 22611 = 4528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22611) = 3 ^ 8 * m + 4528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22611.1, data_15_22611.2]

/-- Complete interval computation for depth 15, residue 22612. -/
theorem bounds_15_22612 : exactInterval 15 22612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22612 : oddCount 22612 15 = 6 ∧ acceleratedOrbit 15 22612 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22612) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22612.1, data_15_22612.2]

/-- Complete interval computation for depth 15, residue 22613. -/
theorem bounds_15_22613 : exactInterval 15 22613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22613 : oddCount 22613 15 = 6 ∧ acceleratedOrbit 15 22613 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22613) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22613.1, data_15_22613.2]

/-- Complete interval computation for depth 15, residue 22614. -/
theorem bounds_15_22614 : exactInterval 15 22614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22614 : oddCount 22614 15 = 7 ∧ acceleratedOrbit 15 22614 = 1511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22614) = 3 ^ 7 * m + 1511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22614.1, data_15_22614.2]

/-- Complete interval computation for depth 15, residue 22615. -/
theorem bounds_15_22615 : exactInterval 15 22615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22615 : oddCount 22615 15 = 7 ∧ acceleratedOrbit 15 22615 = 1511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22615) = 3 ^ 7 * m + 1511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22615.1, data_15_22615.2]

/-- Complete interval computation for depth 15, residue 22616. -/
theorem bounds_15_22616 : exactInterval 15 22616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22616 : oddCount 22616 15 = 8 ∧ acceleratedOrbit 15 22616 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22616) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22616.1, data_15_22616.2]

/-- Complete interval computation for depth 15, residue 22617. -/
theorem bounds_15_22617 : exactInterval 15 22617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22617 : oddCount 22617 15 = 7 ∧ acceleratedOrbit 15 22617 = 1511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22617) = 3 ^ 7 * m + 1511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22617.1, data_15_22617.2]

/-- Complete interval computation for depth 15, residue 22618. -/
theorem bounds_15_22618 : exactInterval 15 22618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22618 : oddCount 22618 15 = 8 ∧ acceleratedOrbit 15 22618 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22618) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22618.1, data_15_22618.2]

/-- Complete interval computation for depth 15, residue 22619. -/
theorem bounds_15_22619 : exactInterval 15 22619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22619 : oddCount 22619 15 = 12 ∧ acceleratedOrbit 15 22619 = 366869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22619) = 3 ^ 12 * m + 366869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22619.1, data_15_22619.2]

/-- Complete interval computation for depth 15, residue 22620. -/
theorem bounds_15_22620 : exactInterval 15 22620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22620 : oddCount 22620 15 = 8 ∧ acceleratedOrbit 15 22620 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22620) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22620.1, data_15_22620.2]

/-- Complete interval computation for depth 15, residue 22621. -/
theorem bounds_15_22621 : exactInterval 15 22621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22621 : oddCount 22621 15 = 8 ∧ acceleratedOrbit 15 22621 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22621) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22621.1, data_15_22621.2]

/-- Complete interval computation for depth 15, residue 22622. -/
theorem bounds_15_22622 : exactInterval 15 22622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22622 : oddCount 22622 15 = 7 ∧ acceleratedOrbit 15 22622 = 1510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22622) = 3 ^ 7 * m + 1510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22622.1, data_15_22622.2]

/-- Complete interval computation for depth 15, residue 22623. -/
theorem bounds_15_22623 : exactInterval 15 22623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22623 : oddCount 22623 15 = 7 ∧ acceleratedOrbit 15 22623 = 1510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22623) = 3 ^ 7 * m + 1510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22623.1, data_15_22623.2]

/-- Complete interval computation for depth 15, residue 22624. -/
theorem bounds_15_22624 : exactInterval 15 22624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22624 : oddCount 22624 15 = 6 ∧ acceleratedOrbit 15 22624 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22624) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22624.1, data_15_22624.2]

/-- Complete interval computation for depth 15, residue 22625. -/
theorem bounds_15_22625 : exactInterval 15 22625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22625 : oddCount 22625 15 = 8 ∧ acceleratedOrbit 15 22625 = 4531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22625) = 3 ^ 8 * m + 4531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22625.1, data_15_22625.2]

/-- Complete interval computation for depth 15, residue 22626. -/
theorem bounds_15_22626 : exactInterval 15 22626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22626 : oddCount 22626 15 = 8 ∧ acceleratedOrbit 15 22626 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22626) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22626.1, data_15_22626.2]

/-- Complete interval computation for depth 15, residue 22627. -/
theorem bounds_15_22627 : exactInterval 15 22627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22627 : oddCount 22627 15 = 8 ∧ acceleratedOrbit 15 22627 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22627) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22627.1, data_15_22627.2]

/-- Complete interval computation for depth 15, residue 22628. -/
theorem bounds_15_22628 : exactInterval 15 22628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22628 : oddCount 22628 15 = 8 ∧ acceleratedOrbit 15 22628 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22628) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22628.1, data_15_22628.2]

/-- Complete interval computation for depth 15, residue 22629. -/
theorem bounds_15_22629 : exactInterval 15 22629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22629 : oddCount 22629 15 = 8 ∧ acceleratedOrbit 15 22629 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22629) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22629.1, data_15_22629.2]

/-- Complete interval computation for depth 15, residue 22630. -/
theorem bounds_15_22630 : exactInterval 15 22630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22630 : oddCount 22630 15 = 8 ∧ acceleratedOrbit 15 22630 = 4535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22630) = 3 ^ 8 * m + 4535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22630.1, data_15_22630.2]

/-- Complete interval computation for depth 15, residue 22631. -/
theorem bounds_15_22631 : exactInterval 15 22631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22631 : oddCount 22631 15 = 11 ∧ acceleratedOrbit 15 22631 = 122354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22631) = 3 ^ 11 * m + 122354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22631.1, data_15_22631.2]

/-- Complete interval computation for depth 15, residue 22632. -/
theorem bounds_15_22632 : exactInterval 15 22632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22632 : oddCount 22632 15 = 6 ∧ acceleratedOrbit 15 22632 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22632) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22632.1, data_15_22632.2]

/-- Complete interval computation for depth 15, residue 22633. -/
theorem bounds_15_22633 : exactInterval 15 22633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22633 : oddCount 22633 15 = 9 ∧ acceleratedOrbit 15 22633 = 13598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22633) = 3 ^ 9 * m + 13598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22633.1, data_15_22633.2]

/-- Complete interval computation for depth 15, residue 22634. -/
theorem bounds_15_22634 : exactInterval 15 22634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22634 : oddCount 22634 15 = 6 ∧ acceleratedOrbit 15 22634 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22634) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22634.1, data_15_22634.2]

/-- Complete interval computation for depth 15, residue 22635. -/
theorem bounds_15_22635 : exactInterval 15 22635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22635 : oddCount 22635 15 = 11 ∧ acceleratedOrbit 15 22635 = 122381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22635) = 3 ^ 11 * m + 122381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22635.1, data_15_22635.2]

/-- Complete interval computation for depth 15, residue 22636. -/
theorem bounds_15_22636 : exactInterval 15 22636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22636 : oddCount 22636 15 = 9 ∧ acceleratedOrbit 15 22636 = 13601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22636) = 3 ^ 9 * m + 13601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22636.1, data_15_22636.2]

/-- Complete interval computation for depth 15, residue 22637. -/
theorem bounds_15_22637 : exactInterval 15 22637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22637 : oddCount 22637 15 = 9 ∧ acceleratedOrbit 15 22637 = 13601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22637) = 3 ^ 9 * m + 13601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22637.1, data_15_22637.2]

/-- Complete interval computation for depth 15, residue 22638. -/
theorem bounds_15_22638 : exactInterval 15 22638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22638 : oddCount 22638 15 = 9 ∧ acceleratedOrbit 15 22638 = 13601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22638) = 3 ^ 9 * m + 13601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22638.1, data_15_22638.2]

/-- Complete interval computation for depth 15, residue 22639. -/
theorem bounds_15_22639 : exactInterval 15 22639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22639 : oddCount 22639 15 = 10 ∧ acceleratedOrbit 15 22639 = 40799 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22639) = 3 ^ 10 * m + 40799 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22639.1, data_15_22639.2]

/-- Complete interval computation for depth 15, residue 22640. -/
theorem bounds_15_22640 : exactInterval 15 22640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22640 : oddCount 22640 15 = 4 ∧ acceleratedOrbit 15 22640 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22640) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22640.1, data_15_22640.2]

/-- Complete interval computation for depth 15, residue 22641. -/
theorem bounds_15_22641 : exactInterval 15 22641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22641 : oddCount 22641 15 = 6 ∧ acceleratedOrbit 15 22641 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22641) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22641.1, data_15_22641.2]

end Collatz.Research.PassageAtlas.Batch0691
