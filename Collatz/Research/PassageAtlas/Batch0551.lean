import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0551

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18022. -/
theorem bounds_15_18022 : exactInterval 15 18022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18022 : oddCount 18022 15 = 7 ∧ acceleratedOrbit 15 18022 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18022) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18022.1, data_15_18022.2]

/-- Complete interval computation for depth 15, residue 18023. -/
theorem bounds_15_18023 : exactInterval 15 18023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18023 : oddCount 18023 15 = 12 ∧ acceleratedOrbit 15 18023 = 292328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18023) = 3 ^ 12 * m + 292328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18023.1, data_15_18023.2]

/-- Complete interval computation for depth 15, residue 18024. -/
theorem bounds_15_18024 : exactInterval 15 18024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18024 : oddCount 18024 15 = 6 ∧ acceleratedOrbit 15 18024 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18024) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18024.1, data_15_18024.2]

/-- Complete interval computation for depth 15, residue 18025. -/
theorem bounds_15_18025 : exactInterval 15 18025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18025 : oddCount 18025 15 = 9 ∧ acceleratedOrbit 15 18025 = 10829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18025) = 3 ^ 9 * m + 10829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18025.1, data_15_18025.2]

/-- Complete interval computation for depth 15, residue 18026. -/
theorem bounds_15_18026 : exactInterval 15 18026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18026 : oddCount 18026 15 = 6 ∧ acceleratedOrbit 15 18026 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18026) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18026.1, data_15_18026.2]

/-- Complete interval computation for depth 15, residue 18027. -/
theorem bounds_15_18027 : exactInterval 15 18027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18027 : oddCount 18027 15 = 8 ∧ acceleratedOrbit 15 18027 = 3610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18027) = 3 ^ 8 * m + 3610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18027.1, data_15_18027.2]

/-- Complete interval computation for depth 15, residue 18028. -/
theorem bounds_15_18028 : exactInterval 15 18028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18028 : oddCount 18028 15 = 8 ∧ acceleratedOrbit 15 18028 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18028) = 3 ^ 8 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18028.1, data_15_18028.2]

/-- Complete interval computation for depth 15, residue 18029. -/
theorem bounds_15_18029 : exactInterval 15 18029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18029 : oddCount 18029 15 = 8 ∧ acceleratedOrbit 15 18029 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18029) = 3 ^ 8 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18029.1, data_15_18029.2]

/-- Complete interval computation for depth 15, residue 18030. -/
theorem bounds_15_18030 : exactInterval 15 18030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18030 : oddCount 18030 15 = 8 ∧ acceleratedOrbit 15 18030 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18030) = 3 ^ 8 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18030.1, data_15_18030.2]

/-- Complete interval computation for depth 15, residue 18031. -/
theorem bounds_15_18031 : exactInterval 15 18031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18031 : oddCount 18031 15 = 8 ∧ acceleratedOrbit 15 18031 = 3611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18031) = 3 ^ 8 * m + 3611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18031.1, data_15_18031.2]

/-- Complete interval computation for depth 15, residue 18032. -/
theorem bounds_15_18032 : exactInterval 15 18032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18032 : oddCount 18032 15 = 9 ∧ acceleratedOrbit 15 18032 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18032) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18032.1, data_15_18032.2]

/-- Complete interval computation for depth 15, residue 18033. -/
theorem bounds_15_18033 : exactInterval 15 18033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18033 : oddCount 18033 15 = 6 ∧ acceleratedOrbit 15 18033 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18033) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18033.1, data_15_18033.2]

/-- Complete interval computation for depth 15, residue 18034. -/
theorem bounds_15_18034 : exactInterval 15 18034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18034 : oddCount 18034 15 = 7 ∧ acceleratedOrbit 15 18034 = 1204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18034) = 3 ^ 7 * m + 1204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18034.1, data_15_18034.2]

/-- Complete interval computation for depth 15, residue 18035. -/
theorem bounds_15_18035 : exactInterval 15 18035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18035 : oddCount 18035 15 = 7 ∧ acceleratedOrbit 15 18035 = 1204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18035) = 3 ^ 7 * m + 1204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18035.1, data_15_18035.2]

/-- Complete interval computation for depth 15, residue 18036. -/
theorem bounds_15_18036 : exactInterval 15 18036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18036 : oddCount 18036 15 = 9 ∧ acceleratedOrbit 15 18036 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18036) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18036.1, data_15_18036.2]

/-- Complete interval computation for depth 15, residue 18037. -/
theorem bounds_15_18037 : exactInterval 15 18037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18037 : oddCount 18037 15 = 9 ∧ acceleratedOrbit 15 18037 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18037) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18037.1, data_15_18037.2]

/-- Complete interval computation for depth 15, residue 18038. -/
theorem bounds_15_18038 : exactInterval 15 18038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18038 : oddCount 18038 15 = 7 ∧ acceleratedOrbit 15 18038 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18038) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18038.1, data_15_18038.2]

/-- Complete interval computation for depth 15, residue 18039. -/
theorem bounds_15_18039 : exactInterval 15 18039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18039 : oddCount 18039 15 = 7 ∧ acceleratedOrbit 15 18039 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18039) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18039.1, data_15_18039.2]

/-- Complete interval computation for depth 15, residue 18040. -/
theorem bounds_15_18040 : exactInterval 15 18040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18040 : oddCount 18040 15 = 9 ∧ acceleratedOrbit 15 18040 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18040) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18040.1, data_15_18040.2]

/-- Complete interval computation for depth 15, residue 18041. -/
theorem bounds_15_18041 : exactInterval 15 18041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18041 : oddCount 18041 15 = 8 ∧ acceleratedOrbit 15 18041 = 3613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18041) = 3 ^ 8 * m + 3613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18041.1, data_15_18041.2]

/-- Complete interval computation for depth 15, residue 18042. -/
theorem bounds_15_18042 : exactInterval 15 18042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18042 : oddCount 18042 15 = 9 ∧ acceleratedOrbit 15 18042 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18042) = 3 ^ 9 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18042.1, data_15_18042.2]

/-- Complete interval computation for depth 15, residue 18043. -/
theorem bounds_15_18043 : exactInterval 15 18043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18043 : oddCount 18043 15 = 7 ∧ acceleratedOrbit 15 18043 = 1205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18043) = 3 ^ 7 * m + 1205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18043.1, data_15_18043.2]

/-- Complete interval computation for depth 15, residue 18044. -/
theorem bounds_15_18044 : exactInterval 15 18044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18044 : oddCount 18044 15 = 10 ∧ acceleratedOrbit 15 18044 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18044) = 3 ^ 10 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18044.1, data_15_18044.2]

/-- Complete interval computation for depth 15, residue 18045. -/
theorem bounds_15_18045 : exactInterval 15 18045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18045 : oddCount 18045 15 = 10 ∧ acceleratedOrbit 15 18045 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18045) = 3 ^ 10 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18045.1, data_15_18045.2]

/-- Complete interval computation for depth 15, residue 18046. -/
theorem bounds_15_18046 : exactInterval 15 18046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18046 : oddCount 18046 15 = 10 ∧ acceleratedOrbit 15 18046 = 32525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18046) = 3 ^ 10 * m + 32525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18046.1, data_15_18046.2]

/-- Complete interval computation for depth 15, residue 18047. -/
theorem bounds_15_18047 : exactInterval 15 18047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18047 : oddCount 18047 15 = 12 ∧ acceleratedOrbit 15 18047 = 292709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18047) = 3 ^ 12 * m + 292709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18047.1, data_15_18047.2]

/-- Complete interval computation for depth 15, residue 18048. -/
theorem bounds_15_18048 : exactInterval 15 18048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18048 : oddCount 18048 15 = 2 ∧ acceleratedOrbit 15 18048 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18048) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18048.1, data_15_18048.2]

/-- Complete interval computation for depth 15, residue 18049. -/
theorem bounds_15_18049 : exactInterval 15 18049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18049 : oddCount 18049 15 = 11 ∧ acceleratedOrbit 15 18049 = 97595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18049) = 3 ^ 11 * m + 97595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18049.1, data_15_18049.2]

/-- Complete interval computation for depth 15, residue 18050. -/
theorem bounds_15_18050 : exactInterval 15 18050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18050 : oddCount 18050 15 = 6 ∧ acceleratedOrbit 15 18050 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18050) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18050.1, data_15_18050.2]

/-- Complete interval computation for depth 15, residue 18051. -/
theorem bounds_15_18051 : exactInterval 15 18051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18051 : oddCount 18051 15 = 6 ∧ acceleratedOrbit 15 18051 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18051) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18051.1, data_15_18051.2]

/-- Complete interval computation for depth 15, residue 18052. -/
theorem bounds_15_18052 : exactInterval 15 18052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18052 : oddCount 18052 15 = 9 ∧ acceleratedOrbit 15 18052 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18052) = 3 ^ 9 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18052.1, data_15_18052.2]

/-- Complete interval computation for depth 15, residue 18053. -/
theorem bounds_15_18053 : exactInterval 15 18053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18053 : oddCount 18053 15 = 9 ∧ acceleratedOrbit 15 18053 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18053) = 3 ^ 9 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18053.1, data_15_18053.2]

/-- Complete interval computation for depth 15, residue 18054. -/
theorem bounds_15_18054 : exactInterval 15 18054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18054 : oddCount 18054 15 = 9 ∧ acceleratedOrbit 15 18054 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18054) = 3 ^ 9 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18054.1, data_15_18054.2]

end Collatz.Research.PassageAtlas.Batch0551
