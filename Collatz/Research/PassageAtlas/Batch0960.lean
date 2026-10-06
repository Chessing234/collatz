import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0960

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31424. -/
theorem bounds_15_31424 : exactInterval 15 31424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31424 : oddCount 31424 15 = 7 ∧ acceleratedOrbit 15 31424 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31424) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31424.1, data_15_31424.2]

/-- Complete interval computation for depth 15, residue 31425. -/
theorem bounds_15_31425 : exactInterval 15 31425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31425 : oddCount 31425 15 = 7 ∧ acceleratedOrbit 15 31425 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31425) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31425.1, data_15_31425.2]

/-- Complete interval computation for depth 15, residue 31426. -/
theorem bounds_15_31426 : exactInterval 15 31426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31426 : oddCount 31426 15 = 7 ∧ acceleratedOrbit 15 31426 = 2098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31426) = 3 ^ 7 * m + 2098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31426.1, data_15_31426.2]

/-- Complete interval computation for depth 15, residue 31427. -/
theorem bounds_15_31427 : exactInterval 15 31427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31427 : oddCount 31427 15 = 7 ∧ acceleratedOrbit 15 31427 = 2098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31427) = 3 ^ 7 * m + 2098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31427.1, data_15_31427.2]

/-- Complete interval computation for depth 15, residue 31428. -/
theorem bounds_15_31428 : exactInterval 15 31428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31428 : oddCount 31428 15 = 6 ∧ acceleratedOrbit 15 31428 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31428) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31428.1, data_15_31428.2]

/-- Complete interval computation for depth 15, residue 31429. -/
theorem bounds_15_31429 : exactInterval 15 31429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31429 : oddCount 31429 15 = 6 ∧ acceleratedOrbit 15 31429 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31429) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31429.1, data_15_31429.2]

/-- Complete interval computation for depth 15, residue 31430. -/
theorem bounds_15_31430 : exactInterval 15 31430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31430 : oddCount 31430 15 = 6 ∧ acceleratedOrbit 15 31430 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31430) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31430.1, data_15_31430.2]

/-- Complete interval computation for depth 15, residue 31431. -/
theorem bounds_15_31431 : exactInterval 15 31431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31431 : oddCount 31431 15 = 7 ∧ acceleratedOrbit 15 31431 = 2098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31431) = 3 ^ 7 * m + 2098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31431.1, data_15_31431.2]

/-- Complete interval computation for depth 15, residue 31432. -/
theorem bounds_15_31432 : exactInterval 15 31432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31432 : oddCount 31432 15 = 6 ∧ acceleratedOrbit 15 31432 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31432) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31432.1, data_15_31432.2]

/-- Complete interval computation for depth 15, residue 31433. -/
theorem bounds_15_31433 : exactInterval 15 31433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31433 : oddCount 31433 15 = 7 ∧ acceleratedOrbit 15 31433 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31433) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31433.1, data_15_31433.2]

/-- Complete interval computation for depth 15, residue 31434. -/
theorem bounds_15_31434 : exactInterval 15 31434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31434 : oddCount 31434 15 = 6 ∧ acceleratedOrbit 15 31434 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31434) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31434.1, data_15_31434.2]

/-- Complete interval computation for depth 15, residue 31435. -/
theorem bounds_15_31435 : exactInterval 15 31435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31435 : oddCount 31435 15 = 9 ∧ acceleratedOrbit 15 31435 = 18886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31435) = 3 ^ 9 * m + 18886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31435.1, data_15_31435.2]

/-- Complete interval computation for depth 15, residue 31436. -/
theorem bounds_15_31436 : exactInterval 15 31436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31436 : oddCount 31436 15 = 6 ∧ acceleratedOrbit 15 31436 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31436) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31436.1, data_15_31436.2]

/-- Complete interval computation for depth 15, residue 31437. -/
theorem bounds_15_31437 : exactInterval 15 31437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31437 : oddCount 31437 15 = 6 ∧ acceleratedOrbit 15 31437 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31437) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31437.1, data_15_31437.2]

/-- Complete interval computation for depth 15, residue 31438. -/
theorem bounds_15_31438 : exactInterval 15 31438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31438 : oddCount 31438 15 = 10 ∧ acceleratedOrbit 15 31438 = 56657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31438) = 3 ^ 10 * m + 56657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31438.1, data_15_31438.2]

/-- Complete interval computation for depth 15, residue 31439. -/
theorem bounds_15_31439 : exactInterval 15 31439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31439 : oddCount 31439 15 = 10 ∧ acceleratedOrbit 15 31439 = 56657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31439) = 3 ^ 10 * m + 56657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31439.1, data_15_31439.2]

/-- Complete interval computation for depth 15, residue 31440. -/
theorem bounds_15_31440 : exactInterval 15 31440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31440 : oddCount 31440 15 = 7 ∧ acceleratedOrbit 15 31440 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31440) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31440.1, data_15_31440.2]

/-- Complete interval computation for depth 15, residue 31441. -/
theorem bounds_15_31441 : exactInterval 15 31441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31441 : oddCount 31441 15 = 7 ∧ acceleratedOrbit 15 31441 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31441) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31441.1, data_15_31441.2]

/-- Complete interval computation for depth 15, residue 31442. -/
theorem bounds_15_31442 : exactInterval 15 31442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31442 : oddCount 31442 15 = 7 ∧ acceleratedOrbit 15 31442 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31442) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31442.1, data_15_31442.2]

/-- Complete interval computation for depth 15, residue 31443. -/
theorem bounds_15_31443 : exactInterval 15 31443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31443 : oddCount 31443 15 = 7 ∧ acceleratedOrbit 15 31443 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31443) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31443.1, data_15_31443.2]

/-- Complete interval computation for depth 15, residue 31444. -/
theorem bounds_15_31444 : exactInterval 15 31444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31444 : oddCount 31444 15 = 7 ∧ acceleratedOrbit 15 31444 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31444) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31444.1, data_15_31444.2]

/-- Complete interval computation for depth 15, residue 31445. -/
theorem bounds_15_31445 : exactInterval 15 31445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31445 : oddCount 31445 15 = 7 ∧ acceleratedOrbit 15 31445 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31445) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31445.1, data_15_31445.2]

/-- Complete interval computation for depth 15, residue 31446. -/
theorem bounds_15_31446 : exactInterval 15 31446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31446 : oddCount 31446 15 = 9 ∧ acceleratedOrbit 15 31446 = 18893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31446) = 3 ^ 9 * m + 18893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31446.1, data_15_31446.2]

/-- Complete interval computation for depth 15, residue 31447. -/
theorem bounds_15_31447 : exactInterval 15 31447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31447 : oddCount 31447 15 = 9 ∧ acceleratedOrbit 15 31447 = 18893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31447) = 3 ^ 9 * m + 18893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31447.1, data_15_31447.2]

/-- Complete interval computation for depth 15, residue 31448. -/
theorem bounds_15_31448 : exactInterval 15 31448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31448 : oddCount 31448 15 = 9 ∧ acceleratedOrbit 15 31448 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31448) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31448.1, data_15_31448.2]

/-- Complete interval computation for depth 15, residue 31449. -/
theorem bounds_15_31449 : exactInterval 15 31449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31449 : oddCount 31449 15 = 6 ∧ acceleratedOrbit 15 31449 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31449) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31449.1, data_15_31449.2]

/-- Complete interval computation for depth 15, residue 31450. -/
theorem bounds_15_31450 : exactInterval 15 31450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31450 : oddCount 31450 15 = 9 ∧ acceleratedOrbit 15 31450 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31450) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31450.1, data_15_31450.2]

/-- Complete interval computation for depth 15, residue 31451. -/
theorem bounds_15_31451 : exactInterval 15 31451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31451 : oddCount 31451 15 = 11 ∧ acceleratedOrbit 15 31451 = 170039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31451) = 3 ^ 11 * m + 170039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31451.1, data_15_31451.2]

/-- Complete interval computation for depth 15, residue 31452. -/
theorem bounds_15_31452 : exactInterval 15 31452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31452 : oddCount 31452 15 = 9 ∧ acceleratedOrbit 15 31452 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31452) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31452.1, data_15_31452.2]

/-- Complete interval computation for depth 15, residue 31453. -/
theorem bounds_15_31453 : exactInterval 15 31453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31453 : oddCount 31453 15 = 9 ∧ acceleratedOrbit 15 31453 = 18899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31453) = 3 ^ 9 * m + 18899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31453.1, data_15_31453.2]

/-- Complete interval computation for depth 15, residue 31454. -/
theorem bounds_15_31454 : exactInterval 15 31454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31454 : oddCount 31454 15 = 8 ∧ acceleratedOrbit 15 31454 = 6299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31454) = 3 ^ 8 * m + 6299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31454.1, data_15_31454.2]

/-- Complete interval computation for depth 15, residue 31455. -/
theorem bounds_15_31455 : exactInterval 15 31455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31455 : oddCount 31455 15 = 8 ∧ acceleratedOrbit 15 31455 = 6299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31455) = 3 ^ 8 * m + 6299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31455.1, data_15_31455.2]

/-- Complete interval computation for depth 15, residue 31456. -/
theorem bounds_15_31456 : exactInterval 15 31456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31456 : oddCount 31456 15 = 7 ∧ acceleratedOrbit 15 31456 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31456) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31456.1, data_15_31456.2]

end Collatz.Research.PassageAtlas.Batch0960
