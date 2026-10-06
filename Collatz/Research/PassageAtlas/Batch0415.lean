import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0415

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13565. -/
theorem bounds_15_13565 : exactInterval 15 13565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13565 : oddCount 13565 15 = 10 ∧ acceleratedOrbit 15 13565 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13565) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13565.1, data_15_13565.2]

/-- Complete interval computation for depth 15, residue 13566. -/
theorem bounds_15_13566 : exactInterval 15 13566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13566 : oddCount 13566 15 = 9 ∧ acceleratedOrbit 15 13566 = 8150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13566) = 3 ^ 9 * m + 8150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13566.1, data_15_13566.2]

/-- Complete interval computation for depth 15, residue 13567. -/
theorem bounds_15_13567 : exactInterval 15 13567 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13567) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13567 : oddCount 13567 15 = 9 ∧ acceleratedOrbit 15 13567 = 8150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13567) = 3 ^ 9 * m + 8150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13567.1, data_15_13567.2]

/-- Complete interval computation for depth 15, residue 13568. -/
theorem bounds_15_13568 : exactInterval 15 13568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13568 : oddCount 13568 15 = 2 ∧ acceleratedOrbit 15 13568 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13568) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13568.1, data_15_13568.2]

/-- Complete interval computation for depth 15, residue 13569. -/
theorem bounds_15_13569 : exactInterval 15 13569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13569 : oddCount 13569 15 = 6 ∧ acceleratedOrbit 15 13569 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13569) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13569.1, data_15_13569.2]

/-- Complete interval computation for depth 15, residue 13570. -/
theorem bounds_15_13570 : exactInterval 15 13570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13570 : oddCount 13570 15 = 9 ∧ acceleratedOrbit 15 13570 = 8156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13570) = 3 ^ 9 * m + 8156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13570.1, data_15_13570.2]

/-- Complete interval computation for depth 15, residue 13571. -/
theorem bounds_15_13571 : exactInterval 15 13571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13571 : oddCount 13571 15 = 9 ∧ acceleratedOrbit 15 13571 = 8156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13571) = 3 ^ 9 * m + 8156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13571.1, data_15_13571.2]

/-- Complete interval computation for depth 15, residue 13572. -/
theorem bounds_15_13572 : exactInterval 15 13572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13572 : oddCount 13572 15 = 5 ∧ acceleratedOrbit 15 13572 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13572) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13572.1, data_15_13572.2]

/-- Complete interval computation for depth 15, residue 13573. -/
theorem bounds_15_13573 : exactInterval 15 13573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13573 : oddCount 13573 15 = 5 ∧ acceleratedOrbit 15 13573 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13573) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13573.1, data_15_13573.2]

/-- Complete interval computation for depth 15, residue 13574. -/
theorem bounds_15_13574 : exactInterval 15 13574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13574 : oddCount 13574 15 = 5 ∧ acceleratedOrbit 15 13574 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13574) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13574.1, data_15_13574.2]

/-- Complete interval computation for depth 15, residue 13575. -/
theorem bounds_15_13575 : exactInterval 15 13575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13575 : oddCount 13575 15 = 9 ∧ acceleratedOrbit 15 13575 = 8156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13575) = 3 ^ 9 * m + 8156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13575.1, data_15_13575.2]

/-- Complete interval computation for depth 15, residue 13576. -/
theorem bounds_15_13576 : exactInterval 15 13576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13576 : oddCount 13576 15 = 7 ∧ acceleratedOrbit 15 13576 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13576) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13576.1, data_15_13576.2]

/-- Complete interval computation for depth 15, residue 13577. -/
theorem bounds_15_13577 : exactInterval 15 13577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13577 : oddCount 13577 15 = 8 ∧ acceleratedOrbit 15 13577 = 2719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13577) = 3 ^ 8 * m + 2719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13577.1, data_15_13577.2]

/-- Complete interval computation for depth 15, residue 13578. -/
theorem bounds_15_13578 : exactInterval 15 13578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13578 : oddCount 13578 15 = 7 ∧ acceleratedOrbit 15 13578 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13578) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13578.1, data_15_13578.2]

/-- Complete interval computation for depth 15, residue 13579. -/
theorem bounds_15_13579 : exactInterval 15 13579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13579 : oddCount 13579 15 = 8 ∧ acceleratedOrbit 15 13579 = 2720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13579) = 3 ^ 8 * m + 2720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13579.1, data_15_13579.2]

/-- Complete interval computation for depth 15, residue 13580. -/
theorem bounds_15_13580 : exactInterval 15 13580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13580 : oddCount 13580 15 = 7 ∧ acceleratedOrbit 15 13580 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13580) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13580.1, data_15_13580.2]

/-- Complete interval computation for depth 15, residue 13581. -/
theorem bounds_15_13581 : exactInterval 15 13581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13581 : oddCount 13581 15 = 7 ∧ acceleratedOrbit 15 13581 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13581) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13581.1, data_15_13581.2]

/-- Complete interval computation for depth 15, residue 13582. -/
theorem bounds_15_13582 : exactInterval 15 13582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13582 : oddCount 13582 15 = 7 ∧ acceleratedOrbit 15 13582 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13582) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13582.1, data_15_13582.2]

/-- Complete interval computation for depth 15, residue 13583. -/
theorem bounds_15_13583 : exactInterval 15 13583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13583 : oddCount 13583 15 = 7 ∧ acceleratedOrbit 15 13583 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13583) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13583.1, data_15_13583.2]

/-- Complete interval computation for depth 15, residue 13584. -/
theorem bounds_15_13584 : exactInterval 15 13584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13584 : oddCount 13584 15 = 7 ∧ acceleratedOrbit 15 13584 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13584) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13584.1, data_15_13584.2]

/-- Complete interval computation for depth 15, residue 13585. -/
theorem bounds_15_13585 : exactInterval 15 13585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13585 : oddCount 13585 15 = 7 ∧ acceleratedOrbit 15 13585 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13585) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13585.1, data_15_13585.2]

/-- Complete interval computation for depth 15, residue 13586. -/
theorem bounds_15_13586 : exactInterval 15 13586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13586 : oddCount 13586 15 = 7 ∧ acceleratedOrbit 15 13586 = 907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13586) = 3 ^ 7 * m + 907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13586.1, data_15_13586.2]

/-- Complete interval computation for depth 15, residue 13587. -/
theorem bounds_15_13587 : exactInterval 15 13587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13587 : oddCount 13587 15 = 7 ∧ acceleratedOrbit 15 13587 = 907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13587) = 3 ^ 7 * m + 907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13587.1, data_15_13587.2]

/-- Complete interval computation for depth 15, residue 13588. -/
theorem bounds_15_13588 : exactInterval 15 13588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13588 : oddCount 13588 15 = 7 ∧ acceleratedOrbit 15 13588 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13588) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13588.1, data_15_13588.2]

/-- Complete interval computation for depth 15, residue 13589. -/
theorem bounds_15_13589 : exactInterval 15 13589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13589 : oddCount 13589 15 = 7 ∧ acceleratedOrbit 15 13589 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13589) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13589.1, data_15_13589.2]

/-- Complete interval computation for depth 15, residue 13590. -/
theorem bounds_15_13590 : exactInterval 15 13590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13590 : oddCount 13590 15 = 7 ∧ acceleratedOrbit 15 13590 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13590) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13590.1, data_15_13590.2]

/-- Complete interval computation for depth 15, residue 13591. -/
theorem bounds_15_13591 : exactInterval 15 13591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13591 : oddCount 13591 15 = 7 ∧ acceleratedOrbit 15 13591 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13591) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13591.1, data_15_13591.2]

/-- Complete interval computation for depth 15, residue 13592. -/
theorem bounds_15_13592 : exactInterval 15 13592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13592 : oddCount 13592 15 = 7 ∧ acceleratedOrbit 15 13592 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13592) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13592.1, data_15_13592.2]

/-- Complete interval computation for depth 15, residue 13593. -/
theorem bounds_15_13593 : exactInterval 15 13593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13593 : oddCount 13593 15 = 10 ∧ acceleratedOrbit 15 13593 = 24502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13593) = 3 ^ 10 * m + 24502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13593.1, data_15_13593.2]

/-- Complete interval computation for depth 15, residue 13594. -/
theorem bounds_15_13594 : exactInterval 15 13594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13594 : oddCount 13594 15 = 7 ∧ acceleratedOrbit 15 13594 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13594) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13594.1, data_15_13594.2]

/-- Complete interval computation for depth 15, residue 13595. -/
theorem bounds_15_13595 : exactInterval 15 13595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13595 : oddCount 13595 15 = 11 ∧ acceleratedOrbit 15 13595 = 73504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13595) = 3 ^ 11 * m + 73504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13595.1, data_15_13595.2]

/-- Complete interval computation for depth 15, residue 13596. -/
theorem bounds_15_13596 : exactInterval 15 13596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13596 : oddCount 13596 15 = 9 ∧ acceleratedOrbit 15 13596 = 8171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13596) = 3 ^ 9 * m + 8171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13596.1, data_15_13596.2]

/-- Complete interval computation for depth 15, residue 13597. -/
theorem bounds_15_13597 : exactInterval 15 13597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13597 : oddCount 13597 15 = 9 ∧ acceleratedOrbit 15 13597 = 8171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13597) = 3 ^ 9 * m + 8171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13597.1, data_15_13597.2]

end Collatz.Research.PassageAtlas.Batch0415
