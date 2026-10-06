import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0765

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25034. -/
theorem bounds_15_25034 : exactInterval 15 25034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25034 : oddCount 25034 15 = 7 ∧ acceleratedOrbit 15 25034 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25034) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25034.1, data_15_25034.2]

/-- Complete interval computation for depth 15, residue 25035. -/
theorem bounds_15_25035 : exactInterval 15 25035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25035 : oddCount 25035 15 = 8 ∧ acceleratedOrbit 15 25035 = 5015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25035) = 3 ^ 8 * m + 5015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25035.1, data_15_25035.2]

/-- Complete interval computation for depth 15, residue 25036. -/
theorem bounds_15_25036 : exactInterval 15 25036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25036 : oddCount 25036 15 = 7 ∧ acceleratedOrbit 15 25036 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25036) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25036.1, data_15_25036.2]

/-- Complete interval computation for depth 15, residue 25037. -/
theorem bounds_15_25037 : exactInterval 15 25037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25037 : oddCount 25037 15 = 7 ∧ acceleratedOrbit 15 25037 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25037) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25037.1, data_15_25037.2]

/-- Complete interval computation for depth 15, residue 25038. -/
theorem bounds_15_25038 : exactInterval 15 25038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25038 : oddCount 25038 15 = 8 ∧ acceleratedOrbit 15 25038 = 5014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25038) = 3 ^ 8 * m + 5014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25038.1, data_15_25038.2]

/-- Complete interval computation for depth 15, residue 25039. -/
theorem bounds_15_25039 : exactInterval 15 25039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25039 : oddCount 25039 15 = 8 ∧ acceleratedOrbit 15 25039 = 5014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25039) = 3 ^ 8 * m + 5014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25039.1, data_15_25039.2]

/-- Complete interval computation for depth 15, residue 25040. -/
theorem bounds_15_25040 : exactInterval 15 25040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25040 : oddCount 25040 15 = 4 ∧ acceleratedOrbit 15 25040 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25040) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25040.1, data_15_25040.2]

/-- Complete interval computation for depth 15, residue 25041. -/
theorem bounds_15_25041 : exactInterval 15 25041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25041 : oddCount 25041 15 = 7 ∧ acceleratedOrbit 15 25041 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25041) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25041.1, data_15_25041.2]

/-- Complete interval computation for depth 15, residue 25042. -/
theorem bounds_15_25042 : exactInterval 15 25042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25042 : oddCount 25042 15 = 8 ∧ acceleratedOrbit 15 25042 = 5015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25042) = 3 ^ 8 * m + 5015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25042.1, data_15_25042.2]

/-- Complete interval computation for depth 15, residue 25043. -/
theorem bounds_15_25043 : exactInterval 15 25043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25043 : oddCount 25043 15 = 8 ∧ acceleratedOrbit 15 25043 = 5015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25043) = 3 ^ 8 * m + 5015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25043.1, data_15_25043.2]

/-- Complete interval computation for depth 15, residue 25044. -/
theorem bounds_15_25044 : exactInterval 15 25044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25044 : oddCount 25044 15 = 4 ∧ acceleratedOrbit 15 25044 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25044) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25044.1, data_15_25044.2]

/-- Complete interval computation for depth 15, residue 25045. -/
theorem bounds_15_25045 : exactInterval 15 25045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25045 : oddCount 25045 15 = 4 ∧ acceleratedOrbit 15 25045 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25045) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25045.1, data_15_25045.2]

/-- Complete interval computation for depth 15, residue 25046. -/
theorem bounds_15_25046 : exactInterval 15 25046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25046 : oddCount 25046 15 = 10 ∧ acceleratedOrbit 15 25046 = 45143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25046) = 3 ^ 10 * m + 45143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25046.1, data_15_25046.2]

/-- Complete interval computation for depth 15, residue 25047. -/
theorem bounds_15_25047 : exactInterval 15 25047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25047 : oddCount 25047 15 = 10 ∧ acceleratedOrbit 15 25047 = 45143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25047) = 3 ^ 10 * m + 45143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25047.1, data_15_25047.2]

/-- Complete interval computation for depth 15, residue 25048. -/
theorem bounds_15_25048 : exactInterval 15 25048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25048 : oddCount 25048 15 = 8 ∧ acceleratedOrbit 15 25048 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25048) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25048.1, data_15_25048.2]

/-- Complete interval computation for depth 15, residue 25049. -/
theorem bounds_15_25049 : exactInterval 15 25049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25049 : oddCount 25049 15 = 8 ∧ acceleratedOrbit 15 25049 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25049) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25049.1, data_15_25049.2]

/-- Complete interval computation for depth 15, residue 25050. -/
theorem bounds_15_25050 : exactInterval 15 25050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25050 : oddCount 25050 15 = 8 ∧ acceleratedOrbit 15 25050 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25050) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25050.1, data_15_25050.2]

/-- Complete interval computation for depth 15, residue 25051. -/
theorem bounds_15_25051 : exactInterval 15 25051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25051 : oddCount 25051 15 = 8 ∧ acceleratedOrbit 15 25051 = 5017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25051) = 3 ^ 8 * m + 5017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25051.1, data_15_25051.2]

/-- Complete interval computation for depth 15, residue 25052. -/
theorem bounds_15_25052 : exactInterval 15 25052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25052 : oddCount 25052 15 = 8 ∧ acceleratedOrbit 15 25052 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25052) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25052.1, data_15_25052.2]

/-- Complete interval computation for depth 15, residue 25053. -/
theorem bounds_15_25053 : exactInterval 15 25053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25053 : oddCount 25053 15 = 8 ∧ acceleratedOrbit 15 25053 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25053) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25053.1, data_15_25053.2]

/-- Complete interval computation for depth 15, residue 25054. -/
theorem bounds_15_25054 : exactInterval 15 25054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25054 : oddCount 25054 15 = 11 ∧ acceleratedOrbit 15 25054 = 135458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25054) = 3 ^ 11 * m + 135458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25054.1, data_15_25054.2]

/-- Complete interval computation for depth 15, residue 25055. -/
theorem bounds_15_25055 : exactInterval 15 25055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25055 : oddCount 25055 15 = 11 ∧ acceleratedOrbit 15 25055 = 135458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25055) = 3 ^ 11 * m + 135458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25055.1, data_15_25055.2]

/-- Complete interval computation for depth 15, residue 25056. -/
theorem bounds_15_25056 : exactInterval 15 25056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25056 : oddCount 25056 15 = 4 ∧ acceleratedOrbit 15 25056 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25056) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25056.1, data_15_25056.2]

/-- Complete interval computation for depth 15, residue 25057. -/
theorem bounds_15_25057 : exactInterval 15 25057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25057 : oddCount 25057 15 = 7 ∧ acceleratedOrbit 15 25057 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25057) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25057.1, data_15_25057.2]

/-- Complete interval computation for depth 15, residue 25058. -/
theorem bounds_15_25058 : exactInterval 15 25058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25058 : oddCount 25058 15 = 4 ∧ acceleratedOrbit 15 25058 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25058) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25058.1, data_15_25058.2]

/-- Complete interval computation for depth 15, residue 25059. -/
theorem bounds_15_25059 : exactInterval 15 25059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25059 : oddCount 25059 15 = 4 ∧ acceleratedOrbit 15 25059 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25059) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25059.1, data_15_25059.2]

/-- Complete interval computation for depth 15, residue 25060. -/
theorem bounds_15_25060 : exactInterval 15 25060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25060 : oddCount 25060 15 = 9 ∧ acceleratedOrbit 15 25060 = 15059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25060) = 3 ^ 9 * m + 15059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25060.1, data_15_25060.2]

/-- Complete interval computation for depth 15, residue 25061. -/
theorem bounds_15_25061 : exactInterval 15 25061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25061 : oddCount 25061 15 = 9 ∧ acceleratedOrbit 15 25061 = 15059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25061) = 3 ^ 9 * m + 15059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25061.1, data_15_25061.2]

/-- Complete interval computation for depth 15, residue 25062. -/
theorem bounds_15_25062 : exactInterval 15 25062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25062 : oddCount 25062 15 = 9 ∧ acceleratedOrbit 15 25062 = 15059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25062) = 3 ^ 9 * m + 15059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25062.1, data_15_25062.2]

/-- Complete interval computation for depth 15, residue 25063. -/
theorem bounds_15_25063 : exactInterval 15 25063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25063 : oddCount 25063 15 = 11 ∧ acceleratedOrbit 15 25063 = 135503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25063) = 3 ^ 11 * m + 135503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25063.1, data_15_25063.2]

/-- Complete interval computation for depth 15, residue 25064. -/
theorem bounds_15_25064 : exactInterval 15 25064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25064 : oddCount 25064 15 = 4 ∧ acceleratedOrbit 15 25064 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25064) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25064.1, data_15_25064.2]

/-- Complete interval computation for depth 15, residue 25065. -/
theorem bounds_15_25065 : exactInterval 15 25065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25065 : oddCount 25065 15 = 7 ∧ acceleratedOrbit 15 25065 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25065) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25065.1, data_15_25065.2]

/-- Complete interval computation for depth 15, residue 25066. -/
theorem bounds_15_25066 : exactInterval 15 25066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25066 : oddCount 25066 15 = 4 ∧ acceleratedOrbit 15 25066 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25066) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25066.1, data_15_25066.2]

end Collatz.Research.PassageAtlas.Batch0765
