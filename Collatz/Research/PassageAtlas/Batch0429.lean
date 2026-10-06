import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0429

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14024. -/
theorem bounds_15_14024 : exactInterval 15 14024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14024 : oddCount 14024 15 = 6 ∧ acceleratedOrbit 15 14024 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14024) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14024.1, data_15_14024.2]

/-- Complete interval computation for depth 15, residue 14025. -/
theorem bounds_15_14025 : exactInterval 15 14025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14025 : oddCount 14025 15 = 8 ∧ acceleratedOrbit 15 14025 = 2810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14025) = 3 ^ 8 * m + 2810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14025.1, data_15_14025.2]

/-- Complete interval computation for depth 15, residue 14026. -/
theorem bounds_15_14026 : exactInterval 15 14026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14026 : oddCount 14026 15 = 6 ∧ acceleratedOrbit 15 14026 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14026) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14026.1, data_15_14026.2]

/-- Complete interval computation for depth 15, residue 14027. -/
theorem bounds_15_14027 : exactInterval 15 14027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14027 : oddCount 14027 15 = 8 ∧ acceleratedOrbit 15 14027 = 2810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14027) = 3 ^ 8 * m + 2810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14027.1, data_15_14027.2]

/-- Complete interval computation for depth 15, residue 14028. -/
theorem bounds_15_14028 : exactInterval 15 14028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14028 : oddCount 14028 15 = 6 ∧ acceleratedOrbit 15 14028 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14028) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14028.1, data_15_14028.2]

/-- Complete interval computation for depth 15, residue 14029. -/
theorem bounds_15_14029 : exactInterval 15 14029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14029 : oddCount 14029 15 = 6 ∧ acceleratedOrbit 15 14029 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14029) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14029.1, data_15_14029.2]

/-- Complete interval computation for depth 15, residue 14030. -/
theorem bounds_15_14030 : exactInterval 15 14030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14030 : oddCount 14030 15 = 9 ∧ acceleratedOrbit 15 14030 = 8429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14030) = 3 ^ 9 * m + 8429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14030.1, data_15_14030.2]

/-- Complete interval computation for depth 15, residue 14031. -/
theorem bounds_15_14031 : exactInterval 15 14031 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14031) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14031 : oddCount 14031 15 = 9 ∧ acceleratedOrbit 15 14031 = 8429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14031) = 3 ^ 9 * m + 8429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14031.1, data_15_14031.2]

/-- Complete interval computation for depth 15, residue 14032. -/
theorem bounds_15_14032 : exactInterval 15 14032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14032 : oddCount 14032 15 = 6 ∧ acceleratedOrbit 15 14032 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14032) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14032.1, data_15_14032.2]

/-- Complete interval computation for depth 15, residue 14033. -/
theorem bounds_15_14033 : exactInterval 15 14033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14033 : oddCount 14033 15 = 7 ∧ acceleratedOrbit 15 14033 = 937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14033) = 3 ^ 7 * m + 937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14033.1, data_15_14033.2]

/-- Complete interval computation for depth 15, residue 14034. -/
theorem bounds_15_14034 : exactInterval 15 14034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14034 : oddCount 14034 15 = 7 ∧ acceleratedOrbit 15 14034 = 937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14034) = 3 ^ 7 * m + 937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14034.1, data_15_14034.2]

/-- Complete interval computation for depth 15, residue 14035. -/
theorem bounds_15_14035 : exactInterval 15 14035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14035 : oddCount 14035 15 = 7 ∧ acceleratedOrbit 15 14035 = 937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14035) = 3 ^ 7 * m + 937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14035.1, data_15_14035.2]

/-- Complete interval computation for depth 15, residue 14036. -/
theorem bounds_15_14036 : exactInterval 15 14036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14036 : oddCount 14036 15 = 6 ∧ acceleratedOrbit 15 14036 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14036) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14036.1, data_15_14036.2]

/-- Complete interval computation for depth 15, residue 14037. -/
theorem bounds_15_14037 : exactInterval 15 14037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14037 : oddCount 14037 15 = 6 ∧ acceleratedOrbit 15 14037 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14037) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14037.1, data_15_14037.2]

/-- Complete interval computation for depth 15, residue 14038. -/
theorem bounds_15_14038 : exactInterval 15 14038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14038 : oddCount 14038 15 = 7 ∧ acceleratedOrbit 15 14038 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14038) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14038.1, data_15_14038.2]

/-- Complete interval computation for depth 15, residue 14039. -/
theorem bounds_15_14039 : exactInterval 15 14039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14039 : oddCount 14039 15 = 7 ∧ acceleratedOrbit 15 14039 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14039) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14039.1, data_15_14039.2]

/-- Complete interval computation for depth 15, residue 14040. -/
theorem bounds_15_14040 : exactInterval 15 14040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14040 : oddCount 14040 15 = 7 ∧ acceleratedOrbit 15 14040 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14040) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14040.1, data_15_14040.2]

/-- Complete interval computation for depth 15, residue 14041. -/
theorem bounds_15_14041 : exactInterval 15 14041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14041 : oddCount 14041 15 = 7 ∧ acceleratedOrbit 15 14041 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14041) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14041.1, data_15_14041.2]

/-- Complete interval computation for depth 15, residue 14042. -/
theorem bounds_15_14042 : exactInterval 15 14042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14042 : oddCount 14042 15 = 7 ∧ acceleratedOrbit 15 14042 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14042) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14042.1, data_15_14042.2]

/-- Complete interval computation for depth 15, residue 14043. -/
theorem bounds_15_14043 : exactInterval 15 14043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14043 : oddCount 14043 15 = 9 ∧ acceleratedOrbit 15 14043 = 8437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14043) = 3 ^ 9 * m + 8437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14043.1, data_15_14043.2]

/-- Complete interval computation for depth 15, residue 14044. -/
theorem bounds_15_14044 : exactInterval 15 14044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14044 : oddCount 14044 15 = 7 ∧ acceleratedOrbit 15 14044 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14044) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14044.1, data_15_14044.2]

/-- Complete interval computation for depth 15, residue 14045. -/
theorem bounds_15_14045 : exactInterval 15 14045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14045 : oddCount 14045 15 = 7 ∧ acceleratedOrbit 15 14045 = 938 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14045) = 3 ^ 7 * m + 938 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14045.1, data_15_14045.2]

/-- Complete interval computation for depth 15, residue 14046. -/
theorem bounds_15_14046 : exactInterval 15 14046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14046 : oddCount 14046 15 = 8 ∧ acceleratedOrbit 15 14046 = 2813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14046) = 3 ^ 8 * m + 2813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14046.1, data_15_14046.2]

/-- Complete interval computation for depth 15, residue 14047. -/
theorem bounds_15_14047 : exactInterval 15 14047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14047 : oddCount 14047 15 = 8 ∧ acceleratedOrbit 15 14047 = 2813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14047) = 3 ^ 8 * m + 2813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14047.1, data_15_14047.2]

/-- Complete interval computation for depth 15, residue 14048. -/
theorem bounds_15_14048 : exactInterval 15 14048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14048 : oddCount 14048 15 = 6 ∧ acceleratedOrbit 15 14048 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14048) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14048.1, data_15_14048.2]

/-- Complete interval computation for depth 15, residue 14049. -/
theorem bounds_15_14049 : exactInterval 15 14049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14049 : oddCount 14049 15 = 9 ∧ acceleratedOrbit 15 14049 = 8441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14049) = 3 ^ 9 * m + 8441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14049.1, data_15_14049.2]

/-- Complete interval computation for depth 15, residue 14050. -/
theorem bounds_15_14050 : exactInterval 15 14050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14050 : oddCount 14050 15 = 6 ∧ acceleratedOrbit 15 14050 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14050) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14050.1, data_15_14050.2]

/-- Complete interval computation for depth 15, residue 14051. -/
theorem bounds_15_14051 : exactInterval 15 14051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14051 : oddCount 14051 15 = 6 ∧ acceleratedOrbit 15 14051 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14051) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14051.1, data_15_14051.2]

/-- Complete interval computation for depth 15, residue 14052. -/
theorem bounds_15_14052 : exactInterval 15 14052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14052 : oddCount 14052 15 = 6 ∧ acceleratedOrbit 15 14052 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14052) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14052.1, data_15_14052.2]

/-- Complete interval computation for depth 15, residue 14053. -/
theorem bounds_15_14053 : exactInterval 15 14053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14053 : oddCount 14053 15 = 6 ∧ acceleratedOrbit 15 14053 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14053) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14053.1, data_15_14053.2]

/-- Complete interval computation for depth 15, residue 14054. -/
theorem bounds_15_14054 : exactInterval 15 14054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14054 : oddCount 14054 15 = 6 ∧ acceleratedOrbit 15 14054 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14054) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14054.1, data_15_14054.2]

/-- Complete interval computation for depth 15, residue 14055. -/
theorem bounds_15_14055 : exactInterval 15 14055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14055 : oddCount 14055 15 = 11 ∧ acceleratedOrbit 15 14055 = 75991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14055) = 3 ^ 11 * m + 75991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14055.1, data_15_14055.2]

/-- Complete interval computation for depth 15, residue 14056. -/
theorem bounds_15_14056 : exactInterval 15 14056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14056 : oddCount 14056 15 = 6 ∧ acceleratedOrbit 15 14056 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14056) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14056.1, data_15_14056.2]

end Collatz.Research.PassageAtlas.Batch0429
