import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0781

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25559. -/
theorem bounds_15_25559 : exactInterval 15 25559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25559 : oddCount 25559 15 = 10 ∧ acceleratedOrbit 15 25559 = 46064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25559) = 3 ^ 10 * m + 46064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25559.1, data_15_25559.2]

/-- Complete interval computation for depth 15, residue 25560. -/
theorem bounds_15_25560 : exactInterval 15 25560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25560 : oddCount 25560 15 = 6 ∧ acceleratedOrbit 15 25560 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25560) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25560.1, data_15_25560.2]

/-- Complete interval computation for depth 15, residue 25561. -/
theorem bounds_15_25561 : exactInterval 15 25561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25561 : oddCount 25561 15 = 5 ∧ acceleratedOrbit 15 25561 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25561) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25561.1, data_15_25561.2]

/-- Complete interval computation for depth 15, residue 25562. -/
theorem bounds_15_25562 : exactInterval 15 25562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25562 : oddCount 25562 15 = 6 ∧ acceleratedOrbit 15 25562 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25562) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25562.1, data_15_25562.2]

/-- Complete interval computation for depth 15, residue 25563. -/
theorem bounds_15_25563 : exactInterval 15 25563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25563 : oddCount 25563 15 = 8 ∧ acceleratedOrbit 15 25563 = 5120 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25563) = 3 ^ 8 * m + 5120 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25563.1, data_15_25563.2]

/-- Complete interval computation for depth 15, residue 25564. -/
theorem bounds_15_25564 : exactInterval 15 25564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25564 : oddCount 25564 15 = 6 ∧ acceleratedOrbit 15 25564 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25564) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25564.1, data_15_25564.2]

/-- Complete interval computation for depth 15, residue 25565. -/
theorem bounds_15_25565 : exactInterval 15 25565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25565 : oddCount 25565 15 = 6 ∧ acceleratedOrbit 15 25565 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25565) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25565.1, data_15_25565.2]

/-- Complete interval computation for depth 15, residue 25566. -/
theorem bounds_15_25566 : exactInterval 15 25566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25566 : oddCount 25566 15 = 11 ∧ acceleratedOrbit 15 25566 = 138226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25566) = 3 ^ 11 * m + 138226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25566.1, data_15_25566.2]

/-- Complete interval computation for depth 15, residue 25567. -/
theorem bounds_15_25567 : exactInterval 15 25567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25567 : oddCount 25567 15 = 11 ∧ acceleratedOrbit 15 25567 = 138226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25567) = 3 ^ 11 * m + 138226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25567.1, data_15_25567.2]

/-- Complete interval computation for depth 15, residue 25568. -/
theorem bounds_15_25568 : exactInterval 15 25568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25568 : oddCount 25568 15 = 7 ∧ acceleratedOrbit 15 25568 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25568) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25568.1, data_15_25568.2]

/-- Complete interval computation for depth 15, residue 25569. -/
theorem bounds_15_25569 : exactInterval 15 25569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25569 : oddCount 25569 15 = 10 ∧ acceleratedOrbit 15 25569 = 46082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25569) = 3 ^ 10 * m + 46082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25569.1, data_15_25569.2]

/-- Complete interval computation for depth 15, residue 25570. -/
theorem bounds_15_25570 : exactInterval 15 25570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25570 : oddCount 25570 15 = 5 ∧ acceleratedOrbit 15 25570 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25570) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25570.1, data_15_25570.2]

/-- Complete interval computation for depth 15, residue 25571. -/
theorem bounds_15_25571 : exactInterval 15 25571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25571 : oddCount 25571 15 = 5 ∧ acceleratedOrbit 15 25571 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25571) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25571.1, data_15_25571.2]

/-- Complete interval computation for depth 15, residue 25572. -/
theorem bounds_15_25572 : exactInterval 15 25572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25572 : oddCount 25572 15 = 8 ∧ acceleratedOrbit 15 25572 = 5123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25572) = 3 ^ 8 * m + 5123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25572.1, data_15_25572.2]

/-- Complete interval computation for depth 15, residue 25573. -/
theorem bounds_15_25573 : exactInterval 15 25573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25573 : oddCount 25573 15 = 8 ∧ acceleratedOrbit 15 25573 = 5123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25573) = 3 ^ 8 * m + 5123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25573.1, data_15_25573.2]

/-- Complete interval computation for depth 15, residue 25574. -/
theorem bounds_15_25574 : exactInterval 15 25574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25574 : oddCount 25574 15 = 8 ∧ acceleratedOrbit 15 25574 = 5123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25574) = 3 ^ 8 * m + 5123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25574.1, data_15_25574.2]

/-- Complete interval computation for depth 15, residue 25575. -/
theorem bounds_15_25575 : exactInterval 15 25575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25575 : oddCount 25575 15 = 6 ∧ acceleratedOrbit 15 25575 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25575) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25575.1, data_15_25575.2]

/-- Complete interval computation for depth 15, residue 25576. -/
theorem bounds_15_25576 : exactInterval 15 25576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25576 : oddCount 25576 15 = 7 ∧ acceleratedOrbit 15 25576 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25576) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25576.1, data_15_25576.2]

/-- Complete interval computation for depth 15, residue 25577. -/
theorem bounds_15_25577 : exactInterval 15 25577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25577 : oddCount 25577 15 = 10 ∧ acceleratedOrbit 15 25577 = 46094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25577) = 3 ^ 10 * m + 46094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25577.1, data_15_25577.2]

/-- Complete interval computation for depth 15, residue 25578. -/
theorem bounds_15_25578 : exactInterval 15 25578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25578 : oddCount 25578 15 = 7 ∧ acceleratedOrbit 15 25578 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25578) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25578.1, data_15_25578.2]

/-- Complete interval computation for depth 15, residue 25579. -/
theorem bounds_15_25579 : exactInterval 15 25579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25579 : oddCount 25579 15 = 8 ∧ acceleratedOrbit 15 25579 = 5122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25579) = 3 ^ 8 * m + 5122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25579.1, data_15_25579.2]

/-- Complete interval computation for depth 15, residue 25580. -/
theorem bounds_15_25580 : exactInterval 15 25580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25580 : oddCount 25580 15 = 10 ∧ acceleratedOrbit 15 25580 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25580) = 3 ^ 10 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25580.1, data_15_25580.2]

/-- Complete interval computation for depth 15, residue 25581. -/
theorem bounds_15_25581 : exactInterval 15 25581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25581 : oddCount 25581 15 = 10 ∧ acceleratedOrbit 15 25581 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25581) = 3 ^ 10 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25581.1, data_15_25581.2]

/-- Complete interval computation for depth 15, residue 25582. -/
theorem bounds_15_25582 : exactInterval 15 25582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25582 : oddCount 25582 15 = 10 ∧ acceleratedOrbit 15 25582 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25582) = 3 ^ 10 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25582.1, data_15_25582.2]

/-- Complete interval computation for depth 15, residue 25583. -/
theorem bounds_15_25583 : exactInterval 15 25583 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25583) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25583 : oddCount 25583 15 = 9 ∧ acceleratedOrbit 15 25583 = 15368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25583) = 3 ^ 9 * m + 15368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25583.1, data_15_25583.2]

/-- Complete interval computation for depth 15, residue 25584. -/
theorem bounds_15_25584 : exactInterval 15 25584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25584 : oddCount 25584 15 = 7 ∧ acceleratedOrbit 15 25584 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25584) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25584.1, data_15_25584.2]

/-- Complete interval computation for depth 15, residue 25585. -/
theorem bounds_15_25585 : exactInterval 15 25585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25585 : oddCount 25585 15 = 7 ∧ acceleratedOrbit 15 25585 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25585) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25585.1, data_15_25585.2]

/-- Complete interval computation for depth 15, residue 25586. -/
theorem bounds_15_25586 : exactInterval 15 25586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25586 : oddCount 25586 15 = 7 ∧ acceleratedOrbit 15 25586 = 1708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25586) = 3 ^ 7 * m + 1708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25586.1, data_15_25586.2]

/-- Complete interval computation for depth 15, residue 25587. -/
theorem bounds_15_25587 : exactInterval 15 25587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25587 : oddCount 25587 15 = 7 ∧ acceleratedOrbit 15 25587 = 1708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25587) = 3 ^ 7 * m + 1708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25587.1, data_15_25587.2]

/-- Complete interval computation for depth 15, residue 25588. -/
theorem bounds_15_25588 : exactInterval 15 25588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25588 : oddCount 25588 15 = 7 ∧ acceleratedOrbit 15 25588 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25588) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25588.1, data_15_25588.2]

/-- Complete interval computation for depth 15, residue 25589. -/
theorem bounds_15_25589 : exactInterval 15 25589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25589 : oddCount 25589 15 = 7 ∧ acceleratedOrbit 15 25589 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25589) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25589.1, data_15_25589.2]

/-- Complete interval computation for depth 15, residue 25590. -/
theorem bounds_15_25590 : exactInterval 15 25590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25590 : oddCount 25590 15 = 8 ∧ acceleratedOrbit 15 25590 = 5125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25590) = 3 ^ 8 * m + 5125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25590.1, data_15_25590.2]

end Collatz.Research.PassageAtlas.Batch0781
