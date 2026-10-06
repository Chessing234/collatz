import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0368

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12025. -/
theorem bounds_15_12025 : exactInterval 15 12025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12025 : oddCount 12025 15 = 7 ∧ acceleratedOrbit 15 12025 = 803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12025) = 3 ^ 7 * m + 803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12025.1, data_15_12025.2]

/-- Complete interval computation for depth 15, residue 12026. -/
theorem bounds_15_12026 : exactInterval 15 12026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12026 : oddCount 12026 15 = 9 ∧ acceleratedOrbit 15 12026 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12026) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12026.1, data_15_12026.2]

/-- Complete interval computation for depth 15, residue 12027. -/
theorem bounds_15_12027 : exactInterval 15 12027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12027 : oddCount 12027 15 = 9 ∧ acceleratedOrbit 15 12027 = 7226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12027) = 3 ^ 9 * m + 7226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12027.1, data_15_12027.2]

/-- Complete interval computation for depth 15, residue 12028. -/
theorem bounds_15_12028 : exactInterval 15 12028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12028 : oddCount 12028 15 = 10 ∧ acceleratedOrbit 15 12028 = 21683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12028) = 3 ^ 10 * m + 21683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12028.1, data_15_12028.2]

/-- Complete interval computation for depth 15, residue 12029. -/
theorem bounds_15_12029 : exactInterval 15 12029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12029 : oddCount 12029 15 = 10 ∧ acceleratedOrbit 15 12029 = 21683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12029) = 3 ^ 10 * m + 21683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12029.1, data_15_12029.2]

/-- Complete interval computation for depth 15, residue 12030. -/
theorem bounds_15_12030 : exactInterval 15 12030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12030 : oddCount 12030 15 = 10 ∧ acceleratedOrbit 15 12030 = 21683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12030) = 3 ^ 10 * m + 21683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12030.1, data_15_12030.2]

/-- Complete interval computation for depth 15, residue 12031. -/
theorem bounds_15_12031 : exactInterval 15 12031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12031 : oddCount 12031 15 = 12 ∧ acceleratedOrbit 15 12031 = 195139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12031) = 3 ^ 12 * m + 195139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12031.1, data_15_12031.2]

/-- Complete interval computation for depth 15, residue 12032. -/
theorem bounds_15_12032 : exactInterval 15 12032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12032 : oddCount 12032 15 = 5 ∧ acceleratedOrbit 15 12032 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12032) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12032.1, data_15_12032.2]

/-- Complete interval computation for depth 15, residue 12033. -/
theorem bounds_15_12033 : exactInterval 15 12033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12033 : oddCount 12033 15 = 6 ∧ acceleratedOrbit 15 12033 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12033) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12033.1, data_15_12033.2]

/-- Complete interval computation for depth 15, residue 12034. -/
theorem bounds_15_12034 : exactInterval 15 12034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12034 : oddCount 12034 15 = 9 ∧ acceleratedOrbit 15 12034 = 7235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12034) = 3 ^ 9 * m + 7235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12034.1, data_15_12034.2]

/-- Complete interval computation for depth 15, residue 12035. -/
theorem bounds_15_12035 : exactInterval 15 12035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12035 : oddCount 12035 15 = 9 ∧ acceleratedOrbit 15 12035 = 7235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12035) = 3 ^ 9 * m + 7235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12035.1, data_15_12035.2]

/-- Complete interval computation for depth 15, residue 12036. -/
theorem bounds_15_12036 : exactInterval 15 12036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12036 : oddCount 12036 15 = 7 ∧ acceleratedOrbit 15 12036 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12036) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12036.1, data_15_12036.2]

/-- Complete interval computation for depth 15, residue 12037. -/
theorem bounds_15_12037 : exactInterval 15 12037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12037 : oddCount 12037 15 = 7 ∧ acceleratedOrbit 15 12037 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12037) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12037.1, data_15_12037.2]

/-- Complete interval computation for depth 15, residue 12038. -/
theorem bounds_15_12038 : exactInterval 15 12038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12038 : oddCount 12038 15 = 7 ∧ acceleratedOrbit 15 12038 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12038) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12038.1, data_15_12038.2]

/-- Complete interval computation for depth 15, residue 12039. -/
theorem bounds_15_12039 : exactInterval 15 12039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12039 : oddCount 12039 15 = 9 ∧ acceleratedOrbit 15 12039 = 7235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12039) = 3 ^ 9 * m + 7235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12039.1, data_15_12039.2]

/-- Complete interval computation for depth 15, residue 12040. -/
theorem bounds_15_12040 : exactInterval 15 12040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12040 : oddCount 12040 15 = 7 ∧ acceleratedOrbit 15 12040 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12040) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12040.1, data_15_12040.2]

/-- Complete interval computation for depth 15, residue 12041. -/
theorem bounds_15_12041 : exactInterval 15 12041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12041 : oddCount 12041 15 = 10 ∧ acceleratedOrbit 15 12041 = 21703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12041) = 3 ^ 10 * m + 21703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12041.1, data_15_12041.2]

/-- Complete interval computation for depth 15, residue 12042. -/
theorem bounds_15_12042 : exactInterval 15 12042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12042 : oddCount 12042 15 = 7 ∧ acceleratedOrbit 15 12042 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12042) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12042.1, data_15_12042.2]

/-- Complete interval computation for depth 15, residue 12043. -/
theorem bounds_15_12043 : exactInterval 15 12043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12043 : oddCount 12043 15 = 6 ∧ acceleratedOrbit 15 12043 = 268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12043) = 3 ^ 6 * m + 268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12043.1, data_15_12043.2]

/-- Complete interval computation for depth 15, residue 12044. -/
theorem bounds_15_12044 : exactInterval 15 12044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12044 : oddCount 12044 15 = 7 ∧ acceleratedOrbit 15 12044 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12044) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12044.1, data_15_12044.2]

/-- Complete interval computation for depth 15, residue 12045. -/
theorem bounds_15_12045 : exactInterval 15 12045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12045 : oddCount 12045 15 = 7 ∧ acceleratedOrbit 15 12045 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12045) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12045.1, data_15_12045.2]

/-- Complete interval computation for depth 15, residue 12046. -/
theorem bounds_15_12046 : exactInterval 15 12046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12046 : oddCount 12046 15 = 7 ∧ acceleratedOrbit 15 12046 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12046) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12046.1, data_15_12046.2]

/-- Complete interval computation for depth 15, residue 12047. -/
theorem bounds_15_12047 : exactInterval 15 12047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12047 : oddCount 12047 15 = 7 ∧ acceleratedOrbit 15 12047 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12047) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12047.1, data_15_12047.2]

/-- Complete interval computation for depth 15, residue 12048. -/
theorem bounds_15_12048 : exactInterval 15 12048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12048 : oddCount 12048 15 = 3 ∧ acceleratedOrbit 15 12048 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12048) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12048.1, data_15_12048.2]

/-- Complete interval computation for depth 15, residue 12049. -/
theorem bounds_15_12049 : exactInterval 15 12049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12049 : oddCount 12049 15 = 7 ∧ acceleratedOrbit 15 12049 = 805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12049) = 3 ^ 7 * m + 805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12049.1, data_15_12049.2]

/-- Complete interval computation for depth 15, residue 12050. -/
theorem bounds_15_12050 : exactInterval 15 12050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12050 : oddCount 12050 15 = 8 ∧ acceleratedOrbit 15 12050 = 2414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12050) = 3 ^ 8 * m + 2414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12050.1, data_15_12050.2]

/-- Complete interval computation for depth 15, residue 12051. -/
theorem bounds_15_12051 : exactInterval 15 12051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12051 : oddCount 12051 15 = 8 ∧ acceleratedOrbit 15 12051 = 2414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12051) = 3 ^ 8 * m + 2414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12051.1, data_15_12051.2]

/-- Complete interval computation for depth 15, residue 12052. -/
theorem bounds_15_12052 : exactInterval 15 12052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12052 : oddCount 12052 15 = 3 ∧ acceleratedOrbit 15 12052 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12052) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12052.1, data_15_12052.2]

/-- Complete interval computation for depth 15, residue 12053. -/
theorem bounds_15_12053 : exactInterval 15 12053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12053 : oddCount 12053 15 = 3 ∧ acceleratedOrbit 15 12053 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12053) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12053.1, data_15_12053.2]

/-- Complete interval computation for depth 15, residue 12054. -/
theorem bounds_15_12054 : exactInterval 15 12054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12054 : oddCount 12054 15 = 10 ∧ acceleratedOrbit 15 12054 = 21734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12054) = 3 ^ 10 * m + 21734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12054.1, data_15_12054.2]

/-- Complete interval computation for depth 15, residue 12055. -/
theorem bounds_15_12055 : exactInterval 15 12055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12055 : oddCount 12055 15 = 10 ∧ acceleratedOrbit 15 12055 = 21734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12055) = 3 ^ 10 * m + 21734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12055.1, data_15_12055.2]

/-- Complete interval computation for depth 15, residue 12056. -/
theorem bounds_15_12056 : exactInterval 15 12056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12056 : oddCount 12056 15 = 3 ∧ acceleratedOrbit 15 12056 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12056) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12056.1, data_15_12056.2]

/-- Complete interval computation for depth 15, residue 12057. -/
theorem bounds_15_12057 : exactInterval 15 12057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12057 : oddCount 12057 15 = 10 ∧ acceleratedOrbit 15 12057 = 21734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12057) = 3 ^ 10 * m + 21734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12057.1, data_15_12057.2]

end Collatz.Research.PassageAtlas.Batch0368
