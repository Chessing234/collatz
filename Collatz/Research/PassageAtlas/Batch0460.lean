import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0460

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15040. -/
theorem bounds_15_15040 : exactInterval 15 15040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15040 : oddCount 15040 15 = 6 ∧ acceleratedOrbit 15 15040 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15040) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15040.1, data_15_15040.2]

/-- Complete interval computation for depth 15, residue 15041. -/
theorem bounds_15_15041 : exactInterval 15 15041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15041 : oddCount 15041 15 = 6 ∧ acceleratedOrbit 15 15041 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15041) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15041.1, data_15_15041.2]

/-- Complete interval computation for depth 15, residue 15042. -/
theorem bounds_15_15042 : exactInterval 15 15042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15042 : oddCount 15042 15 = 8 ∧ acceleratedOrbit 15 15042 = 3014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15042) = 3 ^ 8 * m + 3014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15042.1, data_15_15042.2]

/-- Complete interval computation for depth 15, residue 15043. -/
theorem bounds_15_15043 : exactInterval 15 15043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15043 : oddCount 15043 15 = 8 ∧ acceleratedOrbit 15 15043 = 3014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15043) = 3 ^ 8 * m + 3014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15043.1, data_15_15043.2]

/-- Complete interval computation for depth 15, residue 15044. -/
theorem bounds_15_15044 : exactInterval 15 15044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15044 : oddCount 15044 15 = 5 ∧ acceleratedOrbit 15 15044 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15044) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15044.1, data_15_15044.2]

/-- Complete interval computation for depth 15, residue 15045. -/
theorem bounds_15_15045 : exactInterval 15 15045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15045 : oddCount 15045 15 = 5 ∧ acceleratedOrbit 15 15045 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15045) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15045.1, data_15_15045.2]

/-- Complete interval computation for depth 15, residue 15046. -/
theorem bounds_15_15046 : exactInterval 15 15046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15046 : oddCount 15046 15 = 5 ∧ acceleratedOrbit 15 15046 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15046) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15046.1, data_15_15046.2]

/-- Complete interval computation for depth 15, residue 15047. -/
theorem bounds_15_15047 : exactInterval 15 15047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15047 : oddCount 15047 15 = 8 ∧ acceleratedOrbit 15 15047 = 3014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15047) = 3 ^ 8 * m + 3014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15047.1, data_15_15047.2]

/-- Complete interval computation for depth 15, residue 15048. -/
theorem bounds_15_15048 : exactInterval 15 15048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15048 : oddCount 15048 15 = 5 ∧ acceleratedOrbit 15 15048 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15048) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15048.1, data_15_15048.2]

/-- Complete interval computation for depth 15, residue 15049. -/
theorem bounds_15_15049 : exactInterval 15 15049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15049 : oddCount 15049 15 = 6 ∧ acceleratedOrbit 15 15049 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15049) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15049.1, data_15_15049.2]

/-- Complete interval computation for depth 15, residue 15050. -/
theorem bounds_15_15050 : exactInterval 15 15050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15050 : oddCount 15050 15 = 5 ∧ acceleratedOrbit 15 15050 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15050) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15050.1, data_15_15050.2]

/-- Complete interval computation for depth 15, residue 15051. -/
theorem bounds_15_15051 : exactInterval 15 15051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15051 : oddCount 15051 15 = 10 ∧ acceleratedOrbit 15 15051 = 27134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15051) = 3 ^ 10 * m + 27134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15051.1, data_15_15051.2]

/-- Complete interval computation for depth 15, residue 15052. -/
theorem bounds_15_15052 : exactInterval 15 15052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15052 : oddCount 15052 15 = 5 ∧ acceleratedOrbit 15 15052 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15052) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15052.1, data_15_15052.2]

/-- Complete interval computation for depth 15, residue 15053. -/
theorem bounds_15_15053 : exactInterval 15 15053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15053 : oddCount 15053 15 = 5 ∧ acceleratedOrbit 15 15053 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15053) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15053.1, data_15_15053.2]

/-- Complete interval computation for depth 15, residue 15054. -/
theorem bounds_15_15054 : exactInterval 15 15054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15054 : oddCount 15054 15 = 11 ∧ acceleratedOrbit 15 15054 = 81398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15054) = 3 ^ 11 * m + 81398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15054.1, data_15_15054.2]

/-- Complete interval computation for depth 15, residue 15055. -/
theorem bounds_15_15055 : exactInterval 15 15055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15055 : oddCount 15055 15 = 11 ∧ acceleratedOrbit 15 15055 = 81398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15055) = 3 ^ 11 * m + 81398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15055.1, data_15_15055.2]

/-- Complete interval computation for depth 15, residue 15056. -/
theorem bounds_15_15056 : exactInterval 15 15056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15056 : oddCount 15056 15 = 6 ∧ acceleratedOrbit 15 15056 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15056) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15056.1, data_15_15056.2]

/-- Complete interval computation for depth 15, residue 15057. -/
theorem bounds_15_15057 : exactInterval 15 15057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15057 : oddCount 15057 15 = 8 ∧ acceleratedOrbit 15 15057 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15057) = 3 ^ 8 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15057.1, data_15_15057.2]

/-- Complete interval computation for depth 15, residue 15058. -/
theorem bounds_15_15058 : exactInterval 15 15058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15058 : oddCount 15058 15 = 8 ∧ acceleratedOrbit 15 15058 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15058) = 3 ^ 8 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15058.1, data_15_15058.2]

/-- Complete interval computation for depth 15, residue 15059. -/
theorem bounds_15_15059 : exactInterval 15 15059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15059 : oddCount 15059 15 = 8 ∧ acceleratedOrbit 15 15059 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15059) = 3 ^ 8 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15059.1, data_15_15059.2]

/-- Complete interval computation for depth 15, residue 15060. -/
theorem bounds_15_15060 : exactInterval 15 15060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15060 : oddCount 15060 15 = 6 ∧ acceleratedOrbit 15 15060 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15060) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15060.1, data_15_15060.2]

/-- Complete interval computation for depth 15, residue 15061. -/
theorem bounds_15_15061 : exactInterval 15 15061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15061 : oddCount 15061 15 = 6 ∧ acceleratedOrbit 15 15061 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15061) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15061.1, data_15_15061.2]

/-- Complete interval computation for depth 15, residue 15062. -/
theorem bounds_15_15062 : exactInterval 15 15062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15062 : oddCount 15062 15 = 8 ∧ acceleratedOrbit 15 15062 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15062) = 3 ^ 8 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15062.1, data_15_15062.2]

/-- Complete interval computation for depth 15, residue 15063. -/
theorem bounds_15_15063 : exactInterval 15 15063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15063 : oddCount 15063 15 = 8 ∧ acceleratedOrbit 15 15063 = 3017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15063) = 3 ^ 8 * m + 3017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15063.1, data_15_15063.2]

/-- Complete interval computation for depth 15, residue 15064. -/
theorem bounds_15_15064 : exactInterval 15 15064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15064 : oddCount 15064 15 = 8 ∧ acceleratedOrbit 15 15064 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15064) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15064.1, data_15_15064.2]

/-- Complete interval computation for depth 15, residue 15065. -/
theorem bounds_15_15065 : exactInterval 15 15065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15065 : oddCount 15065 15 = 5 ∧ acceleratedOrbit 15 15065 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15065) = 3 ^ 5 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15065.1, data_15_15065.2]

/-- Complete interval computation for depth 15, residue 15066. -/
theorem bounds_15_15066 : exactInterval 15 15066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15066 : oddCount 15066 15 = 8 ∧ acceleratedOrbit 15 15066 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15066) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15066.1, data_15_15066.2]

/-- Complete interval computation for depth 15, residue 15067. -/
theorem bounds_15_15067 : exactInterval 15 15067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15067 : oddCount 15067 15 = 10 ∧ acceleratedOrbit 15 15067 = 27155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15067) = 3 ^ 10 * m + 27155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15067.1, data_15_15067.2]

/-- Complete interval computation for depth 15, residue 15068. -/
theorem bounds_15_15068 : exactInterval 15 15068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15068 : oddCount 15068 15 = 8 ∧ acceleratedOrbit 15 15068 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15068) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15068.1, data_15_15068.2]

/-- Complete interval computation for depth 15, residue 15069. -/
theorem bounds_15_15069 : exactInterval 15 15069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15069 : oddCount 15069 15 = 8 ∧ acceleratedOrbit 15 15069 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15069) = 3 ^ 8 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15069.1, data_15_15069.2]

/-- Complete interval computation for depth 15, residue 15070. -/
theorem bounds_15_15070 : exactInterval 15 15070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15070 : oddCount 15070 15 = 7 ∧ acceleratedOrbit 15 15070 = 1006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15070) = 3 ^ 7 * m + 1006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15070.1, data_15_15070.2]

/-- Complete interval computation for depth 15, residue 15071. -/
theorem bounds_15_15071 : exactInterval 15 15071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15071 : oddCount 15071 15 = 7 ∧ acceleratedOrbit 15 15071 = 1006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15071) = 3 ^ 7 * m + 1006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15071.1, data_15_15071.2]

/-- Complete interval computation for depth 15, residue 15072. -/
theorem bounds_15_15072 : exactInterval 15 15072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15072 : oddCount 15072 15 = 6 ∧ acceleratedOrbit 15 15072 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15072) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15072.1, data_15_15072.2]

end Collatz.Research.PassageAtlas.Batch0460
