import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0521

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17039. -/
theorem bounds_15_17039 : exactInterval 15 17039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17039 : oddCount 17039 15 = 10 ∧ acceleratedOrbit 15 17039 = 30709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17039) = 3 ^ 10 * m + 30709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17039.1, data_15_17039.2]

/-- Complete interval computation for depth 15, residue 17040. -/
theorem bounds_15_17040 : exactInterval 15 17040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17040 : oddCount 17040 15 = 7 ∧ acceleratedOrbit 15 17040 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17040) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17040.1, data_15_17040.2]

/-- Complete interval computation for depth 15, residue 17041. -/
theorem bounds_15_17041 : exactInterval 15 17041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17041 : oddCount 17041 15 = 7 ∧ acceleratedOrbit 15 17041 = 1138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17041) = 3 ^ 7 * m + 1138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17041.1, data_15_17041.2]

/-- Complete interval computation for depth 15, residue 17042. -/
theorem bounds_15_17042 : exactInterval 15 17042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17042 : oddCount 17042 15 = 7 ∧ acceleratedOrbit 15 17042 = 1138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17042) = 3 ^ 7 * m + 1138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17042.1, data_15_17042.2]

/-- Complete interval computation for depth 15, residue 17043. -/
theorem bounds_15_17043 : exactInterval 15 17043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17043 : oddCount 17043 15 = 7 ∧ acceleratedOrbit 15 17043 = 1138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17043) = 3 ^ 7 * m + 1138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17043.1, data_15_17043.2]

/-- Complete interval computation for depth 15, residue 17044. -/
theorem bounds_15_17044 : exactInterval 15 17044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17044 : oddCount 17044 15 = 7 ∧ acceleratedOrbit 15 17044 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17044) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17044.1, data_15_17044.2]

/-- Complete interval computation for depth 15, residue 17045. -/
theorem bounds_15_17045 : exactInterval 15 17045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17045 : oddCount 17045 15 = 7 ∧ acceleratedOrbit 15 17045 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17045) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17045.1, data_15_17045.2]

/-- Complete interval computation for depth 15, residue 17046. -/
theorem bounds_15_17046 : exactInterval 15 17046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17046 : oddCount 17046 15 = 6 ∧ acceleratedOrbit 15 17046 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17046) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17046.1, data_15_17046.2]

/-- Complete interval computation for depth 15, residue 17047. -/
theorem bounds_15_17047 : exactInterval 15 17047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17047 : oddCount 17047 15 = 6 ∧ acceleratedOrbit 15 17047 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17047) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17047.1, data_15_17047.2]

/-- Complete interval computation for depth 15, residue 17048. -/
theorem bounds_15_17048 : exactInterval 15 17048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17048 : oddCount 17048 15 = 7 ∧ acceleratedOrbit 15 17048 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17048) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17048.1, data_15_17048.2]

/-- Complete interval computation for depth 15, residue 17049. -/
theorem bounds_15_17049 : exactInterval 15 17049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17049 : oddCount 17049 15 = 8 ∧ acceleratedOrbit 15 17049 = 3415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17049) = 3 ^ 8 * m + 3415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17049.1, data_15_17049.2]

/-- Complete interval computation for depth 15, residue 17050. -/
theorem bounds_15_17050 : exactInterval 15 17050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17050 : oddCount 17050 15 = 7 ∧ acceleratedOrbit 15 17050 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17050) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17050.1, data_15_17050.2]

/-- Complete interval computation for depth 15, residue 17051. -/
theorem bounds_15_17051 : exactInterval 15 17051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17051 : oddCount 17051 15 = 11 ∧ acceleratedOrbit 15 17051 = 92188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17051) = 3 ^ 11 * m + 92188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17051.1, data_15_17051.2]

/-- Complete interval computation for depth 15, residue 17052. -/
theorem bounds_15_17052 : exactInterval 15 17052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17052 : oddCount 17052 15 = 10 ∧ acceleratedOrbit 15 17052 = 30739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17052) = 3 ^ 10 * m + 30739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17052.1, data_15_17052.2]

/-- Complete interval computation for depth 15, residue 17053. -/
theorem bounds_15_17053 : exactInterval 15 17053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17053 : oddCount 17053 15 = 10 ∧ acceleratedOrbit 15 17053 = 30739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17053) = 3 ^ 10 * m + 30739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17053.1, data_15_17053.2]

/-- Complete interval computation for depth 15, residue 17054. -/
theorem bounds_15_17054 : exactInterval 15 17054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17054 : oddCount 17054 15 = 10 ∧ acceleratedOrbit 15 17054 = 30739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17054) = 3 ^ 10 * m + 30739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17054.1, data_15_17054.2]

/-- Complete interval computation for depth 15, residue 17055. -/
theorem bounds_15_17055 : exactInterval 15 17055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17055 : oddCount 17055 15 = 10 ∧ acceleratedOrbit 15 17055 = 30736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17055) = 3 ^ 10 * m + 30736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17055.1, data_15_17055.2]

/-- Complete interval computation for depth 15, residue 17056. -/
theorem bounds_15_17056 : exactInterval 15 17056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17056 : oddCount 17056 15 = 4 ∧ acceleratedOrbit 15 17056 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17056) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17056.1, data_15_17056.2]

/-- Complete interval computation for depth 15, residue 17057. -/
theorem bounds_15_17057 : exactInterval 15 17057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17057 : oddCount 17057 15 = 8 ∧ acceleratedOrbit 15 17057 = 3416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17057) = 3 ^ 8 * m + 3416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17057.1, data_15_17057.2]

/-- Complete interval computation for depth 15, residue 17058. -/
theorem bounds_15_17058 : exactInterval 15 17058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17058 : oddCount 17058 15 = 7 ∧ acceleratedOrbit 15 17058 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17058) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17058.1, data_15_17058.2]

/-- Complete interval computation for depth 15, residue 17059. -/
theorem bounds_15_17059 : exactInterval 15 17059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17059 : oddCount 17059 15 = 7 ∧ acceleratedOrbit 15 17059 = 1139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17059) = 3 ^ 7 * m + 1139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17059.1, data_15_17059.2]

/-- Complete interval computation for depth 15, residue 17060. -/
theorem bounds_15_17060 : exactInterval 15 17060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17060 : oddCount 17060 15 = 10 ∧ acceleratedOrbit 15 17060 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17060) = 3 ^ 10 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17060.1, data_15_17060.2]

/-- Complete interval computation for depth 15, residue 17061. -/
theorem bounds_15_17061 : exactInterval 15 17061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17061 : oddCount 17061 15 = 10 ∧ acceleratedOrbit 15 17061 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17061) = 3 ^ 10 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17061.1, data_15_17061.2]

/-- Complete interval computation for depth 15, residue 17062. -/
theorem bounds_15_17062 : exactInterval 15 17062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17062 : oddCount 17062 15 = 10 ∧ acceleratedOrbit 15 17062 = 30755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17062) = 3 ^ 10 * m + 30755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17062.1, data_15_17062.2]

/-- Complete interval computation for depth 15, residue 17063. -/
theorem bounds_15_17063 : exactInterval 15 17063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17063 : oddCount 17063 15 = 10 ∧ acceleratedOrbit 15 17063 = 30752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17063) = 3 ^ 10 * m + 30752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17063.1, data_15_17063.2]

/-- Complete interval computation for depth 15, residue 17064. -/
theorem bounds_15_17064 : exactInterval 15 17064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17064 : oddCount 17064 15 = 4 ∧ acceleratedOrbit 15 17064 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17064) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17064.1, data_15_17064.2]

/-- Complete interval computation for depth 15, residue 17065. -/
theorem bounds_15_17065 : exactInterval 15 17065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17065 : oddCount 17065 15 = 11 ∧ acceleratedOrbit 15 17065 = 92264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17065) = 3 ^ 11 * m + 92264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17065.1, data_15_17065.2]

/-- Complete interval computation for depth 15, residue 17066. -/
theorem bounds_15_17066 : exactInterval 15 17066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17066 : oddCount 17066 15 = 4 ∧ acceleratedOrbit 15 17066 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17066) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17066.1, data_15_17066.2]

/-- Complete interval computation for depth 15, residue 17067. -/
theorem bounds_15_17067 : exactInterval 15 17067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17067 : oddCount 17067 15 = 8 ∧ acceleratedOrbit 15 17067 = 3419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17067) = 3 ^ 8 * m + 3419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17067.1, data_15_17067.2]

/-- Complete interval computation for depth 15, residue 17068. -/
theorem bounds_15_17068 : exactInterval 15 17068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17068 : oddCount 17068 15 = 6 ∧ acceleratedOrbit 15 17068 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17068) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17068.1, data_15_17068.2]

/-- Complete interval computation for depth 15, residue 17069. -/
theorem bounds_15_17069 : exactInterval 15 17069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17069 : oddCount 17069 15 = 6 ∧ acceleratedOrbit 15 17069 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17069) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17069.1, data_15_17069.2]

/-- Complete interval computation for depth 15, residue 17070. -/
theorem bounds_15_17070 : exactInterval 15 17070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17070 : oddCount 17070 15 = 6 ∧ acceleratedOrbit 15 17070 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17070) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17070.1, data_15_17070.2]

/-- Complete interval computation for depth 15, residue 17071. -/
theorem bounds_15_17071 : exactInterval 15 17071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17071 : oddCount 17071 15 = 8 ∧ acceleratedOrbit 15 17071 = 3419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17071) = 3 ^ 8 * m + 3419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17071.1, data_15_17071.2]

end Collatz.Research.PassageAtlas.Batch0521
