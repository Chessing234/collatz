import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0612

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20021. -/
theorem bounds_15_20021 : exactInterval 15 20021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20021 : oddCount 20021 15 = 3 ∧ acceleratedOrbit 15 20021 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20021) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20021.1, data_15_20021.2]

/-- Complete interval computation for depth 15, residue 20022. -/
theorem bounds_15_20022 : exactInterval 15 20022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20022 : oddCount 20022 15 = 12 ∧ acceleratedOrbit 15 20022 = 324769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20022) = 3 ^ 12 * m + 324769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20022.1, data_15_20022.2]

/-- Complete interval computation for depth 15, residue 20023. -/
theorem bounds_15_20023 : exactInterval 15 20023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20023 : oddCount 20023 15 = 12 ∧ acceleratedOrbit 15 20023 = 324769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20023) = 3 ^ 12 * m + 324769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20023.1, data_15_20023.2]

/-- Complete interval computation for depth 15, residue 20024. -/
theorem bounds_15_20024 : exactInterval 15 20024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20024 : oddCount 20024 15 = 8 ∧ acceleratedOrbit 15 20024 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20024) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20024.1, data_15_20024.2]

/-- Complete interval computation for depth 15, residue 20025. -/
theorem bounds_15_20025 : exactInterval 15 20025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20025 : oddCount 20025 15 = 9 ∧ acceleratedOrbit 15 20025 = 12032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20025) = 3 ^ 9 * m + 12032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20025.1, data_15_20025.2]

/-- Complete interval computation for depth 15, residue 20026. -/
theorem bounds_15_20026 : exactInterval 15 20026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20026 : oddCount 20026 15 = 8 ∧ acceleratedOrbit 15 20026 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20026) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20026.1, data_15_20026.2]

/-- Complete interval computation for depth 15, residue 20027. -/
theorem bounds_15_20027 : exactInterval 15 20027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20027 : oddCount 20027 15 = 7 ∧ acceleratedOrbit 15 20027 = 1337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20027) = 3 ^ 7 * m + 1337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20027.1, data_15_20027.2]

/-- Complete interval computation for depth 15, residue 20028. -/
theorem bounds_15_20028 : exactInterval 15 20028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20028 : oddCount 20028 15 = 8 ∧ acceleratedOrbit 15 20028 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20028) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20028.1, data_15_20028.2]

/-- Complete interval computation for depth 15, residue 20029. -/
theorem bounds_15_20029 : exactInterval 15 20029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20029 : oddCount 20029 15 = 8 ∧ acceleratedOrbit 15 20029 = 4013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20029) = 3 ^ 8 * m + 4013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20029.1, data_15_20029.2]

/-- Complete interval computation for depth 15, residue 20030. -/
theorem bounds_15_20030 : exactInterval 15 20030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20030 : oddCount 20030 15 = 7 ∧ acceleratedOrbit 15 20030 = 1337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20030) = 3 ^ 7 * m + 1337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20030.1, data_15_20030.2]

/-- Complete interval computation for depth 15, residue 20031. -/
theorem bounds_15_20031 : exactInterval 15 20031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20031 : oddCount 20031 15 = 7 ∧ acceleratedOrbit 15 20031 = 1337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20031) = 3 ^ 7 * m + 1337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20031.1, data_15_20031.2]

/-- Complete interval computation for depth 15, residue 20032. -/
theorem bounds_15_20032 : exactInterval 15 20032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20032 : oddCount 20032 15 = 6 ∧ acceleratedOrbit 15 20032 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20032) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20032.1, data_15_20032.2]

/-- Complete interval computation for depth 15, residue 20033. -/
theorem bounds_15_20033 : exactInterval 15 20033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20033 : oddCount 20033 15 = 6 ∧ acceleratedOrbit 15 20033 = 446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20033) = 3 ^ 6 * m + 446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20033.1, data_15_20033.2]

/-- Complete interval computation for depth 15, residue 20034. -/
theorem bounds_15_20034 : exactInterval 15 20034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20034 : oddCount 20034 15 = 6 ∧ acceleratedOrbit 15 20034 = 446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20034) = 3 ^ 6 * m + 446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20034.1, data_15_20034.2]

/-- Complete interval computation for depth 15, residue 20035. -/
theorem bounds_15_20035 : exactInterval 15 20035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20035 : oddCount 20035 15 = 6 ∧ acceleratedOrbit 15 20035 = 446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20035) = 3 ^ 6 * m + 446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20035.1, data_15_20035.2]

/-- Complete interval computation for depth 15, residue 20036. -/
theorem bounds_15_20036 : exactInterval 15 20036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20036 : oddCount 20036 15 = 7 ∧ acceleratedOrbit 15 20036 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20036) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20036.1, data_15_20036.2]

/-- Complete interval computation for depth 15, residue 20037. -/
theorem bounds_15_20037 : exactInterval 15 20037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20037 : oddCount 20037 15 = 7 ∧ acceleratedOrbit 15 20037 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20037) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20037.1, data_15_20037.2]

/-- Complete interval computation for depth 15, residue 20038. -/
theorem bounds_15_20038 : exactInterval 15 20038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20038 : oddCount 20038 15 = 7 ∧ acceleratedOrbit 15 20038 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20038) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20038.1, data_15_20038.2]

/-- Complete interval computation for depth 15, residue 20039. -/
theorem bounds_15_20039 : exactInterval 15 20039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20039 : oddCount 20039 15 = 10 ∧ acceleratedOrbit 15 20039 = 36116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20039) = 3 ^ 10 * m + 36116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20039.1, data_15_20039.2]

/-- Complete interval computation for depth 15, residue 20040. -/
theorem bounds_15_20040 : exactInterval 15 20040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20040 : oddCount 20040 15 = 7 ∧ acceleratedOrbit 15 20040 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20040) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20040.1, data_15_20040.2]

/-- Complete interval computation for depth 15, residue 20041. -/
theorem bounds_15_20041 : exactInterval 15 20041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20041 : oddCount 20041 15 = 9 ∧ acceleratedOrbit 15 20041 = 12041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20041) = 3 ^ 9 * m + 12041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20041.1, data_15_20041.2]

/-- Complete interval computation for depth 15, residue 20042. -/
theorem bounds_15_20042 : exactInterval 15 20042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20042 : oddCount 20042 15 = 7 ∧ acceleratedOrbit 15 20042 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20042) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20042.1, data_15_20042.2]

/-- Complete interval computation for depth 15, residue 20043. -/
theorem bounds_15_20043 : exactInterval 15 20043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20043 : oddCount 20043 15 = 7 ∧ acceleratedOrbit 15 20043 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20043) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20043.1, data_15_20043.2]

/-- Complete interval computation for depth 15, residue 20044. -/
theorem bounds_15_20044 : exactInterval 15 20044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20044 : oddCount 20044 15 = 7 ∧ acceleratedOrbit 15 20044 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20044) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20044.1, data_15_20044.2]

/-- Complete interval computation for depth 15, residue 20045. -/
theorem bounds_15_20045 : exactInterval 15 20045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20045 : oddCount 20045 15 = 7 ∧ acceleratedOrbit 15 20045 = 1340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20045) = 3 ^ 7 * m + 1340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20045.1, data_15_20045.2]

/-- Complete interval computation for depth 15, residue 20046. -/
theorem bounds_15_20046 : exactInterval 15 20046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20046 : oddCount 20046 15 = 9 ∧ acceleratedOrbit 15 20046 = 12044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20046) = 3 ^ 9 * m + 12044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20046.1, data_15_20046.2]

/-- Complete interval computation for depth 15, residue 20047. -/
theorem bounds_15_20047 : exactInterval 15 20047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20047 : oddCount 20047 15 = 9 ∧ acceleratedOrbit 15 20047 = 12044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20047) = 3 ^ 9 * m + 12044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20047.1, data_15_20047.2]

/-- Complete interval computation for depth 15, residue 20048. -/
theorem bounds_15_20048 : exactInterval 15 20048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20048 : oddCount 20048 15 = 6 ∧ acceleratedOrbit 15 20048 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20048) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20048.1, data_15_20048.2]

/-- Complete interval computation for depth 15, residue 20049. -/
theorem bounds_15_20049 : exactInterval 15 20049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20049 : oddCount 20049 15 = 8 ∧ acceleratedOrbit 15 20049 = 4016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20049) = 3 ^ 8 * m + 4016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20049.1, data_15_20049.2]

/-- Complete interval computation for depth 15, residue 20050. -/
theorem bounds_15_20050 : exactInterval 15 20050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20050 : oddCount 20050 15 = 8 ∧ acceleratedOrbit 15 20050 = 4016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20050) = 3 ^ 8 * m + 4016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20050.1, data_15_20050.2]

/-- Complete interval computation for depth 15, residue 20051. -/
theorem bounds_15_20051 : exactInterval 15 20051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20051 : oddCount 20051 15 = 8 ∧ acceleratedOrbit 15 20051 = 4016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20051) = 3 ^ 8 * m + 4016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20051.1, data_15_20051.2]

/-- Complete interval computation for depth 15, residue 20052. -/
theorem bounds_15_20052 : exactInterval 15 20052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20052 : oddCount 20052 15 = 6 ∧ acceleratedOrbit 15 20052 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20052) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20052.1, data_15_20052.2]

/-- Complete interval computation for depth 15, residue 20053. -/
theorem bounds_15_20053 : exactInterval 15 20053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20053 : oddCount 20053 15 = 6 ∧ acceleratedOrbit 15 20053 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20053) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20053.1, data_15_20053.2]

end Collatz.Research.PassageAtlas.Batch0612
