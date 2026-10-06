import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0288

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9404. -/
theorem bounds_15_9404 : exactInterval 15 9404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9404 : oddCount 9404 15 = 7 ∧ acceleratedOrbit 15 9404 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9404) = 3 ^ 7 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9404.1, data_15_9404.2]

/-- Complete interval computation for depth 15, residue 9405. -/
theorem bounds_15_9405 : exactInterval 15 9405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9405 : oddCount 9405 15 = 7 ∧ acceleratedOrbit 15 9405 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9405) = 3 ^ 7 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9405.1, data_15_9405.2]

/-- Complete interval computation for depth 15, residue 9406. -/
theorem bounds_15_9406 : exactInterval 15 9406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9406 : oddCount 9406 15 = 7 ∧ acceleratedOrbit 15 9406 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9406) = 3 ^ 7 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9406.1, data_15_9406.2]

/-- Complete interval computation for depth 15, residue 9407. -/
theorem bounds_15_9407 : exactInterval 15 9407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9407 : oddCount 9407 15 = 10 ∧ acceleratedOrbit 15 9407 = 16955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9407) = 3 ^ 10 * m + 16955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9407.1, data_15_9407.2]

/-- Complete interval computation for depth 15, residue 9408. -/
theorem bounds_15_9408 : exactInterval 15 9408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9408 : oddCount 9408 15 = 5 ∧ acceleratedOrbit 15 9408 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9408) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9408.1, data_15_9408.2]

/-- Complete interval computation for depth 15, residue 9409. -/
theorem bounds_15_9409 : exactInterval 15 9409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9409 : oddCount 9409 15 = 7 ∧ acceleratedOrbit 15 9409 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9409) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9409.1, data_15_9409.2]

/-- Complete interval computation for depth 15, residue 9410. -/
theorem bounds_15_9410 : exactInterval 15 9410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9410 : oddCount 9410 15 = 7 ∧ acceleratedOrbit 15 9410 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9410) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9410.1, data_15_9410.2]

/-- Complete interval computation for depth 15, residue 9411. -/
theorem bounds_15_9411 : exactInterval 15 9411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9411 : oddCount 9411 15 = 7 ∧ acceleratedOrbit 15 9411 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9411) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9411.1, data_15_9411.2]

/-- Complete interval computation for depth 15, residue 9412. -/
theorem bounds_15_9412 : exactInterval 15 9412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9412 : oddCount 9412 15 = 5 ∧ acceleratedOrbit 15 9412 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9412) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9412.1, data_15_9412.2]

/-- Complete interval computation for depth 15, residue 9413. -/
theorem bounds_15_9413 : exactInterval 15 9413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9413 : oddCount 9413 15 = 5 ∧ acceleratedOrbit 15 9413 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9413) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9413.1, data_15_9413.2]

/-- Complete interval computation for depth 15, residue 9414. -/
theorem bounds_15_9414 : exactInterval 15 9414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9414 : oddCount 9414 15 = 5 ∧ acceleratedOrbit 15 9414 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9414) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9414.1, data_15_9414.2]

/-- Complete interval computation for depth 15, residue 9415. -/
theorem bounds_15_9415 : exactInterval 15 9415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9415 : oddCount 9415 15 = 7 ∧ acceleratedOrbit 15 9415 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9415) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9415.1, data_15_9415.2]

/-- Complete interval computation for depth 15, residue 9416. -/
theorem bounds_15_9416 : exactInterval 15 9416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9416 : oddCount 9416 15 = 5 ∧ acceleratedOrbit 15 9416 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9416) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9416.1, data_15_9416.2]

/-- Complete interval computation for depth 15, residue 9417. -/
theorem bounds_15_9417 : exactInterval 15 9417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9417 : oddCount 9417 15 = 8 ∧ acceleratedOrbit 15 9417 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9417) = 3 ^ 8 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9417.1, data_15_9417.2]

/-- Complete interval computation for depth 15, residue 9418. -/
theorem bounds_15_9418 : exactInterval 15 9418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9418 : oddCount 9418 15 = 5 ∧ acceleratedOrbit 15 9418 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9418) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9418.1, data_15_9418.2]

/-- Complete interval computation for depth 15, residue 9419. -/
theorem bounds_15_9419 : exactInterval 15 9419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9419 : oddCount 9419 15 = 8 ∧ acceleratedOrbit 15 9419 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9419) = 3 ^ 8 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9419.1, data_15_9419.2]

/-- Complete interval computation for depth 15, residue 9420. -/
theorem bounds_15_9420 : exactInterval 15 9420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9420 : oddCount 9420 15 = 5 ∧ acceleratedOrbit 15 9420 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9420) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9420.1, data_15_9420.2]

/-- Complete interval computation for depth 15, residue 9421. -/
theorem bounds_15_9421 : exactInterval 15 9421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9421 : oddCount 9421 15 = 5 ∧ acceleratedOrbit 15 9421 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9421) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9421.1, data_15_9421.2]

/-- Complete interval computation for depth 15, residue 9422. -/
theorem bounds_15_9422 : exactInterval 15 9422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9422 : oddCount 9422 15 = 7 ∧ acceleratedOrbit 15 9422 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9422) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9422.1, data_15_9422.2]

/-- Complete interval computation for depth 15, residue 9423. -/
theorem bounds_15_9423 : exactInterval 15 9423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9423 : oddCount 9423 15 = 7 ∧ acceleratedOrbit 15 9423 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9423) = 3 ^ 7 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9423.1, data_15_9423.2]

/-- Complete interval computation for depth 15, residue 9424. -/
theorem bounds_15_9424 : exactInterval 15 9424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9424 : oddCount 9424 15 = 5 ∧ acceleratedOrbit 15 9424 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9424) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9424.1, data_15_9424.2]

/-- Complete interval computation for depth 15, residue 9425. -/
theorem bounds_15_9425 : exactInterval 15 9425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9425 : oddCount 9425 15 = 9 ∧ acceleratedOrbit 15 9425 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9425) = 3 ^ 9 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9425.1, data_15_9425.2]

/-- Complete interval computation for depth 15, residue 9426. -/
theorem bounds_15_9426 : exactInterval 15 9426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9426 : oddCount 9426 15 = 9 ∧ acceleratedOrbit 15 9426 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9426) = 3 ^ 9 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9426.1, data_15_9426.2]

/-- Complete interval computation for depth 15, residue 9427. -/
theorem bounds_15_9427 : exactInterval 15 9427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9427 : oddCount 9427 15 = 9 ∧ acceleratedOrbit 15 9427 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9427) = 3 ^ 9 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9427.1, data_15_9427.2]

/-- Complete interval computation for depth 15, residue 9428. -/
theorem bounds_15_9428 : exactInterval 15 9428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9428 : oddCount 9428 15 = 5 ∧ acceleratedOrbit 15 9428 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9428) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9428.1, data_15_9428.2]

/-- Complete interval computation for depth 15, residue 9429. -/
theorem bounds_15_9429 : exactInterval 15 9429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9429 : oddCount 9429 15 = 5 ∧ acceleratedOrbit 15 9429 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9429) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9429.1, data_15_9429.2]

/-- Complete interval computation for depth 15, residue 9430. -/
theorem bounds_15_9430 : exactInterval 15 9430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9430 : oddCount 9430 15 = 9 ∧ acceleratedOrbit 15 9430 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9430) = 3 ^ 9 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9430.1, data_15_9430.2]

/-- Complete interval computation for depth 15, residue 9431. -/
theorem bounds_15_9431 : exactInterval 15 9431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9431 : oddCount 9431 15 = 9 ∧ acceleratedOrbit 15 9431 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9431) = 3 ^ 9 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9431.1, data_15_9431.2]

/-- Complete interval computation for depth 15, residue 9432. -/
theorem bounds_15_9432 : exactInterval 15 9432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9432 : oddCount 9432 15 = 8 ∧ acceleratedOrbit 15 9432 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9432) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9432.1, data_15_9432.2]

/-- Complete interval computation for depth 15, residue 9433. -/
theorem bounds_15_9433 : exactInterval 15 9433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9433 : oddCount 9433 15 = 5 ∧ acceleratedOrbit 15 9433 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9433) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9433.1, data_15_9433.2]

/-- Complete interval computation for depth 15, residue 9434. -/
theorem bounds_15_9434 : exactInterval 15 9434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9434 : oddCount 9434 15 = 8 ∧ acceleratedOrbit 15 9434 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9434) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9434.1, data_15_9434.2]

/-- Complete interval computation for depth 15, residue 9435. -/
theorem bounds_15_9435 : exactInterval 15 9435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9435 : oddCount 9435 15 = 10 ∧ acceleratedOrbit 15 9435 = 17009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9435) = 3 ^ 10 * m + 17009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9435.1, data_15_9435.2]

/-- Complete interval computation for depth 15, residue 9436. -/
theorem bounds_15_9436 : exactInterval 15 9436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9436 : oddCount 9436 15 = 8 ∧ acceleratedOrbit 15 9436 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9436) = 3 ^ 8 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9436.1, data_15_9436.2]

end Collatz.Research.PassageAtlas.Batch0288
