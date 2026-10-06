import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0307

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10027. -/
theorem bounds_15_10027 : exactInterval 15 10027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10027 : oddCount 10027 15 = 7 ∧ acceleratedOrbit 15 10027 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10027) = 3 ^ 7 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10027.1, data_15_10027.2]

/-- Complete interval computation for depth 15, residue 10028. -/
theorem bounds_15_10028 : exactInterval 15 10028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10028 : oddCount 10028 15 = 6 ∧ acceleratedOrbit 15 10028 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10028) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10028.1, data_15_10028.2]

/-- Complete interval computation for depth 15, residue 10029. -/
theorem bounds_15_10029 : exactInterval 15 10029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10029 : oddCount 10029 15 = 6 ∧ acceleratedOrbit 15 10029 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10029) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10029.1, data_15_10029.2]

/-- Complete interval computation for depth 15, residue 10030. -/
theorem bounds_15_10030 : exactInterval 15 10030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10030 : oddCount 10030 15 = 6 ∧ acceleratedOrbit 15 10030 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10030) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10030.1, data_15_10030.2]

/-- Complete interval computation for depth 15, residue 10031. -/
theorem bounds_15_10031 : exactInterval 15 10031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10031 : oddCount 10031 15 = 8 ∧ acceleratedOrbit 15 10031 = 2009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10031) = 3 ^ 8 * m + 2009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10031.1, data_15_10031.2]

/-- Complete interval computation for depth 15, residue 10032. -/
theorem bounds_15_10032 : exactInterval 15 10032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10032 : oddCount 10032 15 = 7 ∧ acceleratedOrbit 15 10032 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10032) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10032.1, data_15_10032.2]

/-- Complete interval computation for depth 15, residue 10033. -/
theorem bounds_15_10033 : exactInterval 15 10033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10033 : oddCount 10033 15 = 6 ∧ acceleratedOrbit 15 10033 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10033) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10033.1, data_15_10033.2]

/-- Complete interval computation for depth 15, residue 10034. -/
theorem bounds_15_10034 : exactInterval 15 10034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10034 : oddCount 10034 15 = 6 ∧ acceleratedOrbit 15 10034 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10034) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10034.1, data_15_10034.2]

/-- Complete interval computation for depth 15, residue 10035. -/
theorem bounds_15_10035 : exactInterval 15 10035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10035 : oddCount 10035 15 = 6 ∧ acceleratedOrbit 15 10035 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10035) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10035.1, data_15_10035.2]

/-- Complete interval computation for depth 15, residue 10036. -/
theorem bounds_15_10036 : exactInterval 15 10036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10036 : oddCount 10036 15 = 7 ∧ acceleratedOrbit 15 10036 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10036) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10036.1, data_15_10036.2]

/-- Complete interval computation for depth 15, residue 10037. -/
theorem bounds_15_10037 : exactInterval 15 10037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10037 : oddCount 10037 15 = 7 ∧ acceleratedOrbit 15 10037 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10037) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10037.1, data_15_10037.2]

/-- Complete interval computation for depth 15, residue 10038. -/
theorem bounds_15_10038 : exactInterval 15 10038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10038 : oddCount 10038 15 = 8 ∧ acceleratedOrbit 15 10038 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10038) = 3 ^ 8 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10038.1, data_15_10038.2]

/-- Complete interval computation for depth 15, residue 10039. -/
theorem bounds_15_10039 : exactInterval 15 10039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10039 : oddCount 10039 15 = 8 ∧ acceleratedOrbit 15 10039 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10039) = 3 ^ 8 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10039.1, data_15_10039.2]

/-- Complete interval computation for depth 15, residue 10040. -/
theorem bounds_15_10040 : exactInterval 15 10040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10040 : oddCount 10040 15 = 9 ∧ acceleratedOrbit 15 10040 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10040) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10040.1, data_15_10040.2]

/-- Complete interval computation for depth 15, residue 10041. -/
theorem bounds_15_10041 : exactInterval 15 10041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10041 : oddCount 10041 15 = 9 ∧ acceleratedOrbit 15 10041 = 6034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10041) = 3 ^ 9 * m + 6034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10041.1, data_15_10041.2]

/-- Complete interval computation for depth 15, residue 10042. -/
theorem bounds_15_10042 : exactInterval 15 10042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10042 : oddCount 10042 15 = 9 ∧ acceleratedOrbit 15 10042 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10042) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10042.1, data_15_10042.2]

/-- Complete interval computation for depth 15, residue 10043. -/
theorem bounds_15_10043 : exactInterval 15 10043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10043 : oddCount 10043 15 = 6 ∧ acceleratedOrbit 15 10043 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10043) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10043.1, data_15_10043.2]

/-- Complete interval computation for depth 15, residue 10044. -/
theorem bounds_15_10044 : exactInterval 15 10044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10044 : oddCount 10044 15 = 9 ∧ acceleratedOrbit 15 10044 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10044) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10044.1, data_15_10044.2]

/-- Complete interval computation for depth 15, residue 10045. -/
theorem bounds_15_10045 : exactInterval 15 10045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10045 : oddCount 10045 15 = 9 ∧ acceleratedOrbit 15 10045 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10045) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10045.1, data_15_10045.2]

/-- Complete interval computation for depth 15, residue 10046. -/
theorem bounds_15_10046 : exactInterval 15 10046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10046 : oddCount 10046 15 = 8 ∧ acceleratedOrbit 15 10046 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10046) = 3 ^ 8 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10046.1, data_15_10046.2]

/-- Complete interval computation for depth 15, residue 10047. -/
theorem bounds_15_10047 : exactInterval 15 10047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10047 : oddCount 10047 15 = 8 ∧ acceleratedOrbit 15 10047 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10047) = 3 ^ 8 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10047.1, data_15_10047.2]

/-- Complete interval computation for depth 15, residue 10048. -/
theorem bounds_15_10048 : exactInterval 15 10048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10048 : oddCount 10048 15 = 5 ∧ acceleratedOrbit 15 10048 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10048) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10048.1, data_15_10048.2]

/-- Complete interval computation for depth 15, residue 10049. -/
theorem bounds_15_10049 : exactInterval 15 10049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10049 : oddCount 10049 15 = 7 ∧ acceleratedOrbit 15 10049 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10049) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10049.1, data_15_10049.2]

/-- Complete interval computation for depth 15, residue 10050. -/
theorem bounds_15_10050 : exactInterval 15 10050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10050 : oddCount 10050 15 = 8 ∧ acceleratedOrbit 15 10050 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10050) = 3 ^ 8 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10050.1, data_15_10050.2]

/-- Complete interval computation for depth 15, residue 10051. -/
theorem bounds_15_10051 : exactInterval 15 10051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10051 : oddCount 10051 15 = 8 ∧ acceleratedOrbit 15 10051 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10051) = 3 ^ 8 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10051.1, data_15_10051.2]

/-- Complete interval computation for depth 15, residue 10052. -/
theorem bounds_15_10052 : exactInterval 15 10052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10052 : oddCount 10052 15 = 7 ∧ acceleratedOrbit 15 10052 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10052) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10052.1, data_15_10052.2]

/-- Complete interval computation for depth 15, residue 10053. -/
theorem bounds_15_10053 : exactInterval 15 10053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10053 : oddCount 10053 15 = 7 ∧ acceleratedOrbit 15 10053 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10053) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10053.1, data_15_10053.2]

/-- Complete interval computation for depth 15, residue 10054. -/
theorem bounds_15_10054 : exactInterval 15 10054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10054 : oddCount 10054 15 = 7 ∧ acceleratedOrbit 15 10054 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10054) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10054.1, data_15_10054.2]

/-- Complete interval computation for depth 15, residue 10055. -/
theorem bounds_15_10055 : exactInterval 15 10055 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10055) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10055 : oddCount 10055 15 = 9 ∧ acceleratedOrbit 15 10055 = 6041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10055) = 3 ^ 9 * m + 6041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10055.1, data_15_10055.2]

/-- Complete interval computation for depth 15, residue 10056. -/
theorem bounds_15_10056 : exactInterval 15 10056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10056 : oddCount 10056 15 = 6 ∧ acceleratedOrbit 15 10056 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10056) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10056.1, data_15_10056.2]

/-- Complete interval computation for depth 15, residue 10057. -/
theorem bounds_15_10057 : exactInterval 15 10057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10057 : oddCount 10057 15 = 8 ∧ acceleratedOrbit 15 10057 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10057) = 3 ^ 8 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10057.1, data_15_10057.2]

/-- Complete interval computation for depth 15, residue 10058. -/
theorem bounds_15_10058 : exactInterval 15 10058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10058 : oddCount 10058 15 = 6 ∧ acceleratedOrbit 15 10058 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10058) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10058.1, data_15_10058.2]

end Collatz.Research.PassageAtlas.Batch0307
