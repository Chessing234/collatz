import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0197

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6422. -/
theorem bounds_15_6422 : exactInterval 15 6422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6422 : oddCount 6422 15 = 6 ∧ acceleratedOrbit 15 6422 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6422) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6422.1, data_15_6422.2]

/-- Complete interval computation for depth 15, residue 6423. -/
theorem bounds_15_6423 : exactInterval 15 6423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6423 : oddCount 6423 15 = 6 ∧ acceleratedOrbit 15 6423 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6423) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6423.1, data_15_6423.2]

/-- Complete interval computation for depth 15, residue 6424. -/
theorem bounds_15_6424 : exactInterval 15 6424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6424 : oddCount 6424 15 = 4 ∧ acceleratedOrbit 15 6424 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6424) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6424.1, data_15_6424.2]

/-- Complete interval computation for depth 15, residue 6425. -/
theorem bounds_15_6425 : exactInterval 15 6425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6425 : oddCount 6425 15 = 6 ∧ acceleratedOrbit 15 6425 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6425) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6425.1, data_15_6425.2]

/-- Complete interval computation for depth 15, residue 6426. -/
theorem bounds_15_6426 : exactInterval 15 6426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6426 : oddCount 6426 15 = 4 ∧ acceleratedOrbit 15 6426 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6426) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6426.1, data_15_6426.2]

/-- Complete interval computation for depth 15, residue 6427. -/
theorem bounds_15_6427 : exactInterval 15 6427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6427 : oddCount 6427 15 = 10 ∧ acceleratedOrbit 15 6427 = 11585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6427) = 3 ^ 10 * m + 11585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6427.1, data_15_6427.2]

/-- Complete interval computation for depth 15, residue 6428. -/
theorem bounds_15_6428 : exactInterval 15 6428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6428 : oddCount 6428 15 = 8 ∧ acceleratedOrbit 15 6428 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6428) = 3 ^ 8 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6428.1, data_15_6428.2]

/-- Complete interval computation for depth 15, residue 6429. -/
theorem bounds_15_6429 : exactInterval 15 6429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6429 : oddCount 6429 15 = 8 ∧ acceleratedOrbit 15 6429 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6429) = 3 ^ 8 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6429.1, data_15_6429.2]

/-- Complete interval computation for depth 15, residue 6430. -/
theorem bounds_15_6430 : exactInterval 15 6430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6430 : oddCount 6430 15 = 8 ∧ acceleratedOrbit 15 6430 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6430) = 3 ^ 8 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6430.1, data_15_6430.2]

/-- Complete interval computation for depth 15, residue 6431. -/
theorem bounds_15_6431 : exactInterval 15 6431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6431 : oddCount 6431 15 = 8 ∧ acceleratedOrbit 15 6431 = 1288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6431) = 3 ^ 8 * m + 1288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6431.1, data_15_6431.2]

/-- Complete interval computation for depth 15, residue 6432. -/
theorem bounds_15_6432 : exactInterval 15 6432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6432 : oddCount 6432 15 = 4 ∧ acceleratedOrbit 15 6432 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6432) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6432.1, data_15_6432.2]

/-- Complete interval computation for depth 15, residue 6433. -/
theorem bounds_15_6433 : exactInterval 15 6433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6433 : oddCount 6433 15 = 7 ∧ acceleratedOrbit 15 6433 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6433) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6433.1, data_15_6433.2]

/-- Complete interval computation for depth 15, residue 6434. -/
theorem bounds_15_6434 : exactInterval 15 6434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6434 : oddCount 6434 15 = 8 ∧ acceleratedOrbit 15 6434 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6434) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6434.1, data_15_6434.2]

/-- Complete interval computation for depth 15, residue 6435. -/
theorem bounds_15_6435 : exactInterval 15 6435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6435 : oddCount 6435 15 = 8 ∧ acceleratedOrbit 15 6435 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6435) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6435.1, data_15_6435.2]

/-- Complete interval computation for depth 15, residue 6436. -/
theorem bounds_15_6436 : exactInterval 15 6436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6436 : oddCount 6436 15 = 8 ∧ acceleratedOrbit 15 6436 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6436) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6436.1, data_15_6436.2]

/-- Complete interval computation for depth 15, residue 6437. -/
theorem bounds_15_6437 : exactInterval 15 6437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6437 : oddCount 6437 15 = 8 ∧ acceleratedOrbit 15 6437 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6437) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6437.1, data_15_6437.2]

/-- Complete interval computation for depth 15, residue 6438. -/
theorem bounds_15_6438 : exactInterval 15 6438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6438 : oddCount 6438 15 = 8 ∧ acceleratedOrbit 15 6438 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6438) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6438.1, data_15_6438.2]

/-- Complete interval computation for depth 15, residue 6439. -/
theorem bounds_15_6439 : exactInterval 15 6439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6439 : oddCount 6439 15 = 10 ∧ acceleratedOrbit 15 6439 = 11609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6439) = 3 ^ 10 * m + 11609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6439.1, data_15_6439.2]

/-- Complete interval computation for depth 15, residue 6440. -/
theorem bounds_15_6440 : exactInterval 15 6440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6440 : oddCount 6440 15 = 4 ∧ acceleratedOrbit 15 6440 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6440) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6440.1, data_15_6440.2]

/-- Complete interval computation for depth 15, residue 6441. -/
theorem bounds_15_6441 : exactInterval 15 6441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6441 : oddCount 6441 15 = 7 ∧ acceleratedOrbit 15 6441 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6441) = 3 ^ 7 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6441.1, data_15_6441.2]

/-- Complete interval computation for depth 15, residue 6442. -/
theorem bounds_15_6442 : exactInterval 15 6442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6442 : oddCount 6442 15 = 4 ∧ acceleratedOrbit 15 6442 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6442) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6442.1, data_15_6442.2]

/-- Complete interval computation for depth 15, residue 6443. -/
theorem bounds_15_6443 : exactInterval 15 6443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6443 : oddCount 6443 15 = 8 ∧ acceleratedOrbit 15 6443 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6443) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6443.1, data_15_6443.2]

/-- Complete interval computation for depth 15, residue 6444. -/
theorem bounds_15_6444 : exactInterval 15 6444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6444 : oddCount 6444 15 = 4 ∧ acceleratedOrbit 15 6444 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6444) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6444.1, data_15_6444.2]

/-- Complete interval computation for depth 15, residue 6445. -/
theorem bounds_15_6445 : exactInterval 15 6445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6445 : oddCount 6445 15 = 4 ∧ acceleratedOrbit 15 6445 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6445) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6445.1, data_15_6445.2]

/-- Complete interval computation for depth 15, residue 6446. -/
theorem bounds_15_6446 : exactInterval 15 6446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6446 : oddCount 6446 15 = 4 ∧ acceleratedOrbit 15 6446 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6446) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6446.1, data_15_6446.2]

/-- Complete interval computation for depth 15, residue 6447. -/
theorem bounds_15_6447 : exactInterval 15 6447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6447 : oddCount 6447 15 = 9 ∧ acceleratedOrbit 15 6447 = 3874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6447) = 3 ^ 9 * m + 3874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6447.1, data_15_6447.2]

/-- Complete interval computation for depth 15, residue 6448. -/
theorem bounds_15_6448 : exactInterval 15 6448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6448 : oddCount 6448 15 = 4 ∧ acceleratedOrbit 15 6448 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6448) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6448.1, data_15_6448.2]

/-- Complete interval computation for depth 15, residue 6449. -/
theorem bounds_15_6449 : exactInterval 15 6449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6449 : oddCount 6449 15 = 8 ∧ acceleratedOrbit 15 6449 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6449) = 3 ^ 8 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6449.1, data_15_6449.2]

/-- Complete interval computation for depth 15, residue 6450. -/
theorem bounds_15_6450 : exactInterval 15 6450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6450 : oddCount 6450 15 = 8 ∧ acceleratedOrbit 15 6450 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6450) = 3 ^ 8 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6450.1, data_15_6450.2]

/-- Complete interval computation for depth 15, residue 6451. -/
theorem bounds_15_6451 : exactInterval 15 6451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6451 : oddCount 6451 15 = 8 ∧ acceleratedOrbit 15 6451 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6451) = 3 ^ 8 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6451.1, data_15_6451.2]

/-- Complete interval computation for depth 15, residue 6452. -/
theorem bounds_15_6452 : exactInterval 15 6452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6452 : oddCount 6452 15 = 4 ∧ acceleratedOrbit 15 6452 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6452) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6452.1, data_15_6452.2]

/-- Complete interval computation for depth 15, residue 6453. -/
theorem bounds_15_6453 : exactInterval 15 6453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6453 : oddCount 6453 15 = 4 ∧ acceleratedOrbit 15 6453 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6453) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6453.1, data_15_6453.2]

/-- Complete interval computation for depth 15, residue 6454. -/
theorem bounds_15_6454 : exactInterval 15 6454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6454 : oddCount 6454 15 = 11 ∧ acceleratedOrbit 15 6454 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6454) = 3 ^ 11 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6454.1, data_15_6454.2]

end Collatz.Research.PassageAtlas.Batch0197
