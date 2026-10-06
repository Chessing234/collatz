import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0887

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29032. -/
theorem bounds_15_29032 : exactInterval 15 29032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29032 : oddCount 29032 15 = 7 ∧ acceleratedOrbit 15 29032 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29032) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29032.1, data_15_29032.2]

/-- Complete interval computation for depth 15, residue 29033. -/
theorem bounds_15_29033 : exactInterval 15 29033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29033 : oddCount 29033 15 = 6 ∧ acceleratedOrbit 15 29033 = 646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29033) = 3 ^ 6 * m + 646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29033.1, data_15_29033.2]

/-- Complete interval computation for depth 15, residue 29034. -/
theorem bounds_15_29034 : exactInterval 15 29034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29034 : oddCount 29034 15 = 7 ∧ acceleratedOrbit 15 29034 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29034) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29034.1, data_15_29034.2]

/-- Complete interval computation for depth 15, residue 29035. -/
theorem bounds_15_29035 : exactInterval 15 29035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29035 : oddCount 29035 15 = 6 ∧ acceleratedOrbit 15 29035 = 646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29035) = 3 ^ 6 * m + 646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29035.1, data_15_29035.2]

/-- Complete interval computation for depth 15, residue 29036. -/
theorem bounds_15_29036 : exactInterval 15 29036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29036 : oddCount 29036 15 = 8 ∧ acceleratedOrbit 15 29036 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29036) = 3 ^ 8 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29036.1, data_15_29036.2]

/-- Complete interval computation for depth 15, residue 29037. -/
theorem bounds_15_29037 : exactInterval 15 29037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29037 : oddCount 29037 15 = 8 ∧ acceleratedOrbit 15 29037 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29037) = 3 ^ 8 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29037.1, data_15_29037.2]

/-- Complete interval computation for depth 15, residue 29038. -/
theorem bounds_15_29038 : exactInterval 15 29038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29038 : oddCount 29038 15 = 8 ∧ acceleratedOrbit 15 29038 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29038) = 3 ^ 8 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29038.1, data_15_29038.2]

/-- Complete interval computation for depth 15, residue 29039. -/
theorem bounds_15_29039 : exactInterval 15 29039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29039 : oddCount 29039 15 = 8 ∧ acceleratedOrbit 15 29039 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29039) = 3 ^ 8 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29039.1, data_15_29039.2]

/-- Complete interval computation for depth 15, residue 29040. -/
theorem bounds_15_29040 : exactInterval 15 29040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29040 : oddCount 29040 15 = 7 ∧ acceleratedOrbit 15 29040 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29040) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29040.1, data_15_29040.2]

/-- Complete interval computation for depth 15, residue 29041. -/
theorem bounds_15_29041 : exactInterval 15 29041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29041 : oddCount 29041 15 = 7 ∧ acceleratedOrbit 15 29041 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29041) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29041.1, data_15_29041.2]

/-- Complete interval computation for depth 15, residue 29042. -/
theorem bounds_15_29042 : exactInterval 15 29042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29042 : oddCount 29042 15 = 7 ∧ acceleratedOrbit 15 29042 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29042) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29042.1, data_15_29042.2]

/-- Complete interval computation for depth 15, residue 29043. -/
theorem bounds_15_29043 : exactInterval 15 29043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29043 : oddCount 29043 15 = 7 ∧ acceleratedOrbit 15 29043 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29043) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29043.1, data_15_29043.2]

/-- Complete interval computation for depth 15, residue 29044. -/
theorem bounds_15_29044 : exactInterval 15 29044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29044 : oddCount 29044 15 = 7 ∧ acceleratedOrbit 15 29044 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29044) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29044.1, data_15_29044.2]

/-- Complete interval computation for depth 15, residue 29045. -/
theorem bounds_15_29045 : exactInterval 15 29045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29045 : oddCount 29045 15 = 7 ∧ acceleratedOrbit 15 29045 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29045) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29045.1, data_15_29045.2]

/-- Complete interval computation for depth 15, residue 29046. -/
theorem bounds_15_29046 : exactInterval 15 29046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29046 : oddCount 29046 15 = 10 ∧ acceleratedOrbit 15 29046 = 52352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29046) = 3 ^ 10 * m + 52352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29046.1, data_15_29046.2]

/-- Complete interval computation for depth 15, residue 29047. -/
theorem bounds_15_29047 : exactInterval 15 29047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29047 : oddCount 29047 15 = 10 ∧ acceleratedOrbit 15 29047 = 52352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29047) = 3 ^ 10 * m + 52352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29047.1, data_15_29047.2]

/-- Complete interval computation for depth 15, residue 29048. -/
theorem bounds_15_29048 : exactInterval 15 29048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29048 : oddCount 29048 15 = 9 ∧ acceleratedOrbit 15 29048 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29048) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29048.1, data_15_29048.2]

/-- Complete interval computation for depth 15, residue 29049. -/
theorem bounds_15_29049 : exactInterval 15 29049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29049 : oddCount 29049 15 = 11 ∧ acceleratedOrbit 15 29049 = 157054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29049) = 3 ^ 11 * m + 157054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29049.1, data_15_29049.2]

/-- Complete interval computation for depth 15, residue 29050. -/
theorem bounds_15_29050 : exactInterval 15 29050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29050 : oddCount 29050 15 = 9 ∧ acceleratedOrbit 15 29050 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29050) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29050.1, data_15_29050.2]

/-- Complete interval computation for depth 15, residue 29051. -/
theorem bounds_15_29051 : exactInterval 15 29051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29051 : oddCount 29051 15 = 9 ∧ acceleratedOrbit 15 29051 = 17452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29051) = 3 ^ 9 * m + 17452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29051.1, data_15_29051.2]

/-- Complete interval computation for depth 15, residue 29052. -/
theorem bounds_15_29052 : exactInterval 15 29052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29052 : oddCount 29052 15 = 9 ∧ acceleratedOrbit 15 29052 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29052) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29052.1, data_15_29052.2]

/-- Complete interval computation for depth 15, residue 29053. -/
theorem bounds_15_29053 : exactInterval 15 29053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29053 : oddCount 29053 15 = 9 ∧ acceleratedOrbit 15 29053 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29053) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29053.1, data_15_29053.2]

/-- Complete interval computation for depth 15, residue 29054. -/
theorem bounds_15_29054 : exactInterval 15 29054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29054 : oddCount 29054 15 = 8 ∧ acceleratedOrbit 15 29054 = 5818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29054) = 3 ^ 8 * m + 5818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29054.1, data_15_29054.2]

/-- Complete interval computation for depth 15, residue 29055. -/
theorem bounds_15_29055 : exactInterval 15 29055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29055 : oddCount 29055 15 = 8 ∧ acceleratedOrbit 15 29055 = 5818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29055) = 3 ^ 8 * m + 5818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29055.1, data_15_29055.2]

/-- Complete interval computation for depth 15, residue 29056. -/
theorem bounds_15_29056 : exactInterval 15 29056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29056 : oddCount 29056 15 = 2 ∧ acceleratedOrbit 15 29056 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29056) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29056.1, data_15_29056.2]

/-- Complete interval computation for depth 15, residue 29057. -/
theorem bounds_15_29057 : exactInterval 15 29057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29057 : oddCount 29057 15 = 6 ∧ acceleratedOrbit 15 29057 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29057) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29057.1, data_15_29057.2]

/-- Complete interval computation for depth 15, residue 29058. -/
theorem bounds_15_29058 : exactInterval 15 29058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29058 : oddCount 29058 15 = 8 ∧ acceleratedOrbit 15 29058 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29058) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29058.1, data_15_29058.2]

/-- Complete interval computation for depth 15, residue 29059. -/
theorem bounds_15_29059 : exactInterval 15 29059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29059 : oddCount 29059 15 = 8 ∧ acceleratedOrbit 15 29059 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29059) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29059.1, data_15_29059.2]

/-- Complete interval computation for depth 15, residue 29060. -/
theorem bounds_15_29060 : exactInterval 15 29060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29060 : oddCount 29060 15 = 8 ∧ acceleratedOrbit 15 29060 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29060) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29060.1, data_15_29060.2]

/-- Complete interval computation for depth 15, residue 29061. -/
theorem bounds_15_29061 : exactInterval 15 29061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29061 : oddCount 29061 15 = 8 ∧ acceleratedOrbit 15 29061 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29061) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29061.1, data_15_29061.2]

/-- Complete interval computation for depth 15, residue 29062. -/
theorem bounds_15_29062 : exactInterval 15 29062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29062 : oddCount 29062 15 = 8 ∧ acceleratedOrbit 15 29062 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29062) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29062.1, data_15_29062.2]

/-- Complete interval computation for depth 15, residue 29063. -/
theorem bounds_15_29063 : exactInterval 15 29063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29063 : oddCount 29063 15 = 8 ∧ acceleratedOrbit 15 29063 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29063) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29063.1, data_15_29063.2]

/-- Complete interval computation for depth 15, residue 29064. -/
theorem bounds_15_29064 : exactInterval 15 29064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29064 : oddCount 29064 15 = 8 ∧ acceleratedOrbit 15 29064 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29064) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29064.1, data_15_29064.2]

end Collatz.Research.PassageAtlas.Batch0887
