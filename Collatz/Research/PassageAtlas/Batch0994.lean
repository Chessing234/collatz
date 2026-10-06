import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0994

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32538. -/
theorem bounds_15_32538 : exactInterval 15 32538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32538 : oddCount 32538 15 = 6 ∧ acceleratedOrbit 15 32538 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32538) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32538.1, data_15_32538.2]

/-- Complete interval computation for depth 15, residue 32539. -/
theorem bounds_15_32539 : exactInterval 15 32539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32539 : oddCount 32539 15 = 13 ∧ acceleratedOrbit 15 32539 = 1583252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32539) = 3 ^ 13 * m + 1583252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32539.1, data_15_32539.2]

/-- Complete interval computation for depth 15, residue 32540. -/
theorem bounds_15_32540 : exactInterval 15 32540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32540 : oddCount 32540 15 = 8 ∧ acceleratedOrbit 15 32540 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32540) = 3 ^ 8 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32540.1, data_15_32540.2]

/-- Complete interval computation for depth 15, residue 32541. -/
theorem bounds_15_32541 : exactInterval 15 32541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32541 : oddCount 32541 15 = 8 ∧ acceleratedOrbit 15 32541 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32541) = 3 ^ 8 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32541.1, data_15_32541.2]

/-- Complete interval computation for depth 15, residue 32542. -/
theorem bounds_15_32542 : exactInterval 15 32542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32542 : oddCount 32542 15 = 8 ∧ acceleratedOrbit 15 32542 = 6517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32542) = 3 ^ 8 * m + 6517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32542.1, data_15_32542.2]

/-- Complete interval computation for depth 15, residue 32543. -/
theorem bounds_15_32543 : exactInterval 15 32543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32543 : oddCount 32543 15 = 9 ∧ acceleratedOrbit 15 32543 = 19549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32543) = 3 ^ 9 * m + 19549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32543.1, data_15_32543.2]

/-- Complete interval computation for depth 15, residue 32544. -/
theorem bounds_15_32544 : exactInterval 15 32544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32544 : oddCount 32544 15 = 7 ∧ acceleratedOrbit 15 32544 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32544) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32544.1, data_15_32544.2]

/-- Complete interval computation for depth 15, residue 32545. -/
theorem bounds_15_32545 : exactInterval 15 32545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32545 : oddCount 32545 15 = 7 ∧ acceleratedOrbit 15 32545 = 2173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32545) = 3 ^ 7 * m + 2173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32545.1, data_15_32545.2]

/-- Complete interval computation for depth 15, residue 32546. -/
theorem bounds_15_32546 : exactInterval 15 32546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32546 : oddCount 32546 15 = 8 ∧ acceleratedOrbit 15 32546 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32546) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32546.1, data_15_32546.2]

/-- Complete interval computation for depth 15, residue 32547. -/
theorem bounds_15_32547 : exactInterval 15 32547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32547 : oddCount 32547 15 = 8 ∧ acceleratedOrbit 15 32547 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32547) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32547.1, data_15_32547.2]

/-- Complete interval computation for depth 15, residue 32548. -/
theorem bounds_15_32548 : exactInterval 15 32548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32548 : oddCount 32548 15 = 8 ∧ acceleratedOrbit 15 32548 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32548) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32548.1, data_15_32548.2]

/-- Complete interval computation for depth 15, residue 32549. -/
theorem bounds_15_32549 : exactInterval 15 32549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32549 : oddCount 32549 15 = 8 ∧ acceleratedOrbit 15 32549 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32549) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32549.1, data_15_32549.2]

/-- Complete interval computation for depth 15, residue 32550. -/
theorem bounds_15_32550 : exactInterval 15 32550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32550 : oddCount 32550 15 = 8 ∧ acceleratedOrbit 15 32550 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32550) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32550.1, data_15_32550.2]

/-- Complete interval computation for depth 15, residue 32551. -/
theorem bounds_15_32551 : exactInterval 15 32551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32551 : oddCount 32551 15 = 8 ∧ acceleratedOrbit 15 32551 = 6518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32551) = 3 ^ 8 * m + 6518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32551.1, data_15_32551.2]

/-- Complete interval computation for depth 15, residue 32552. -/
theorem bounds_15_32552 : exactInterval 15 32552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32552 : oddCount 32552 15 = 7 ∧ acceleratedOrbit 15 32552 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32552) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32552.1, data_15_32552.2]

/-- Complete interval computation for depth 15, residue 32553. -/
theorem bounds_15_32553 : exactInterval 15 32553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32553 : oddCount 32553 15 = 7 ∧ acceleratedOrbit 15 32553 = 2173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32553) = 3 ^ 7 * m + 2173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32553.1, data_15_32553.2]

/-- Complete interval computation for depth 15, residue 32554. -/
theorem bounds_15_32554 : exactInterval 15 32554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32554 : oddCount 32554 15 = 7 ∧ acceleratedOrbit 15 32554 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32554) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32554.1, data_15_32554.2]

/-- Complete interval computation for depth 15, residue 32555. -/
theorem bounds_15_32555 : exactInterval 15 32555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32555 : oddCount 32555 15 = 8 ∧ acceleratedOrbit 15 32555 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32555) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32555.1, data_15_32555.2]

/-- Complete interval computation for depth 15, residue 32556. -/
theorem bounds_15_32556 : exactInterval 15 32556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32556 : oddCount 32556 15 = 5 ∧ acceleratedOrbit 15 32556 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32556) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32556.1, data_15_32556.2]

/-- Complete interval computation for depth 15, residue 32557. -/
theorem bounds_15_32557 : exactInterval 15 32557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32557 : oddCount 32557 15 = 5 ∧ acceleratedOrbit 15 32557 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32557) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32557.1, data_15_32557.2]

/-- Complete interval computation for depth 15, residue 32558. -/
theorem bounds_15_32558 : exactInterval 15 32558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32558 : oddCount 32558 15 = 5 ∧ acceleratedOrbit 15 32558 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32558) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32558.1, data_15_32558.2]

/-- Complete interval computation for depth 15, residue 32559. -/
theorem bounds_15_32559 : exactInterval 15 32559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32559 : oddCount 32559 15 = 8 ∧ acceleratedOrbit 15 32559 = 6520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32559) = 3 ^ 8 * m + 6520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32559.1, data_15_32559.2]

/-- Complete interval computation for depth 15, residue 32560. -/
theorem bounds_15_32560 : exactInterval 15 32560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32560 : oddCount 32560 15 = 7 ∧ acceleratedOrbit 15 32560 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32560) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32560.1, data_15_32560.2]

/-- Complete interval computation for depth 15, residue 32561. -/
theorem bounds_15_32561 : exactInterval 15 32561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32561 : oddCount 32561 15 = 5 ∧ acceleratedOrbit 15 32561 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32561) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32561.1, data_15_32561.2]

/-- Complete interval computation for depth 15, residue 32562. -/
theorem bounds_15_32562 : exactInterval 15 32562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32562 : oddCount 32562 15 = 5 ∧ acceleratedOrbit 15 32562 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32562) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32562.1, data_15_32562.2]

/-- Complete interval computation for depth 15, residue 32563. -/
theorem bounds_15_32563 : exactInterval 15 32563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32563 : oddCount 32563 15 = 5 ∧ acceleratedOrbit 15 32563 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32563) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32563.1, data_15_32563.2]

/-- Complete interval computation for depth 15, residue 32564. -/
theorem bounds_15_32564 : exactInterval 15 32564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32564 : oddCount 32564 15 = 7 ∧ acceleratedOrbit 15 32564 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32564) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32564.1, data_15_32564.2]

/-- Complete interval computation for depth 15, residue 32565. -/
theorem bounds_15_32565 : exactInterval 15 32565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32565 : oddCount 32565 15 = 7 ∧ acceleratedOrbit 15 32565 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32565) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32565.1, data_15_32565.2]

/-- Complete interval computation for depth 15, residue 32566. -/
theorem bounds_15_32566 : exactInterval 15 32566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32566 : oddCount 32566 15 = 9 ∧ acceleratedOrbit 15 32566 = 19565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32566) = 3 ^ 9 * m + 19565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32566.1, data_15_32566.2]

/-- Complete interval computation for depth 15, residue 32567. -/
theorem bounds_15_32567 : exactInterval 15 32567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32567 : oddCount 32567 15 = 9 ∧ acceleratedOrbit 15 32567 = 19565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32567) = 3 ^ 9 * m + 19565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32567.1, data_15_32567.2]

/-- Complete interval computation for depth 15, residue 32568. -/
theorem bounds_15_32568 : exactInterval 15 32568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32568 : oddCount 32568 15 = 8 ∧ acceleratedOrbit 15 32568 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32568) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32568.1, data_15_32568.2]

/-- Complete interval computation for depth 15, residue 32569. -/
theorem bounds_15_32569 : exactInterval 15 32569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32569 : oddCount 32569 15 = 7 ∧ acceleratedOrbit 15 32569 = 2174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32569) = 3 ^ 7 * m + 2174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32569.1, data_15_32569.2]

/-- Complete interval computation for depth 15, residue 32570. -/
theorem bounds_15_32570 : exactInterval 15 32570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32570 : oddCount 32570 15 = 8 ∧ acceleratedOrbit 15 32570 = 6524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32570) = 3 ^ 8 * m + 6524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32570.1, data_15_32570.2]

end Collatz.Research.PassageAtlas.Batch0994
