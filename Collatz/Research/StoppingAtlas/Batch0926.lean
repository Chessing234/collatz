import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0926

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7040. -/
theorem bounds_13_7040 : exactInterval 13 7040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7040 : oddCount 7040 13 = 4 ∧ acceleratedOrbit 13 7040 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7040) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7040.1, data_13_7040.2]

/-- Complete interval computation for depth 13, residue 7041. -/
theorem bounds_13_7041 : exactInterval 13 7041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7041 : oddCount 7041 13 = 9 ∧ acceleratedOrbit 13 7041 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7041) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7041.1, data_13_7041.2]

/-- Complete interval computation for depth 13, residue 7042. -/
theorem bounds_13_7042 : exactInterval 13 7042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7042 : oddCount 7042 13 = 7 ∧ acceleratedOrbit 13 7042 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7042) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7042.1, data_13_7042.2]

/-- Complete interval computation for depth 13, residue 7043. -/
theorem bounds_13_7043 : exactInterval 13 7043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7043 : oddCount 7043 13 = 7 ∧ acceleratedOrbit 13 7043 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7043) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7043.1, data_13_7043.2]

/-- Complete interval computation for depth 13, residue 7044. -/
theorem bounds_13_7044 : exactInterval 13 7044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7044 : oddCount 7044 13 = 7 ∧ acceleratedOrbit 13 7044 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7044) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7044.1, data_13_7044.2]

/-- Complete interval computation for depth 13, residue 7045. -/
theorem bounds_13_7045 : exactInterval 13 7045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7045 : oddCount 7045 13 = 7 ∧ acceleratedOrbit 13 7045 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7045) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7045.1, data_13_7045.2]

/-- Complete interval computation for depth 13, residue 7046. -/
theorem bounds_13_7046 : exactInterval 13 7046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7046 : oddCount 7046 13 = 7 ∧ acceleratedOrbit 13 7046 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7046) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7046.1, data_13_7046.2]

/-- Complete interval computation for depth 13, residue 7047. -/
theorem bounds_13_7047 : exactInterval 13 7047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7047) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7047 : oddCount 7047 13 = 7 ∧ acceleratedOrbit 13 7047 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7047) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7047.1, data_13_7047.2]

/-- Complete interval computation for depth 13, residue 7048. -/
theorem bounds_13_7048 : exactInterval 13 7048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7048 : oddCount 7048 13 = 4 ∧ acceleratedOrbit 13 7048 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7048) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7048.1, data_13_7048.2]

/-- Complete interval computation for depth 13, residue 7049. -/
theorem bounds_13_7049 : exactInterval 13 7049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7049 : oddCount 7049 13 = 9 ∧ acceleratedOrbit 13 7049 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7049) = 3 ^ 9 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7049.1, data_13_7049.2]

/-- Complete interval computation for depth 13, residue 7050. -/
theorem bounds_13_7050 : exactInterval 13 7050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7050 : oddCount 7050 13 = 4 ∧ acceleratedOrbit 13 7050 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7050) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7050.1, data_13_7050.2]

/-- Complete interval computation for depth 13, residue 7051. -/
theorem bounds_13_7051 : exactInterval 13 7051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7051 : oddCount 7051 13 = 9 ∧ acceleratedOrbit 13 7051 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7051) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7051.1, data_13_7051.2]

/-- Complete interval computation for depth 13, residue 7052. -/
theorem bounds_13_7052 : exactInterval 13 7052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7052 : oddCount 7052 13 = 4 ∧ acceleratedOrbit 13 7052 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7052) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7052.1, data_13_7052.2]

/-- Complete interval computation for depth 13, residue 7053. -/
theorem bounds_13_7053 : exactInterval 13 7053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7053 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7053) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7053 : oddCount 7053 13 = 4 ∧ acceleratedOrbit 13 7053 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7053 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7053) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7053.1, data_13_7053.2]

/-- Complete interval computation for depth 13, residue 7054. -/
theorem bounds_13_7054 : exactInterval 13 7054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7054 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7054) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7054 : oddCount 7054 13 = 6 ∧ acceleratedOrbit 13 7054 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7054 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7054) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7054.1, data_13_7054.2]

end Collatz.Research.StoppingAtlas.Batch0926
