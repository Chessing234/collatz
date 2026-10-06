import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0216

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7045. -/
theorem bounds_15_7045 : exactInterval 15 7045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7045 : oddCount 7045 15 = 9 ∧ acceleratedOrbit 15 7045 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7045) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7045.1, data_15_7045.2]

/-- Complete interval computation for depth 15, residue 7046. -/
theorem bounds_15_7046 : exactInterval 15 7046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7046 : oddCount 7046 15 = 9 ∧ acceleratedOrbit 15 7046 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7046) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7046.1, data_15_7046.2]

/-- Complete interval computation for depth 15, residue 7047. -/
theorem bounds_15_7047 : exactInterval 15 7047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7047 : oddCount 7047 15 = 9 ∧ acceleratedOrbit 15 7047 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7047) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7047.1, data_15_7047.2]

/-- Complete interval computation for depth 15, residue 7048. -/
theorem bounds_15_7048 : exactInterval 15 7048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7048 : oddCount 7048 15 = 6 ∧ acceleratedOrbit 15 7048 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7048) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7048.1, data_15_7048.2]

/-- Complete interval computation for depth 15, residue 7049. -/
theorem bounds_15_7049 : exactInterval 15 7049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7049 : oddCount 7049 15 = 10 ∧ acceleratedOrbit 15 7049 = 12707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7049) = 3 ^ 10 * m + 12707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7049.1, data_15_7049.2]

/-- Complete interval computation for depth 15, residue 7050. -/
theorem bounds_15_7050 : exactInterval 15 7050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7050 : oddCount 7050 15 = 6 ∧ acceleratedOrbit 15 7050 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7050) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7050.1, data_15_7050.2]

/-- Complete interval computation for depth 15, residue 7051. -/
theorem bounds_15_7051 : exactInterval 15 7051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7051 : oddCount 7051 15 = 10 ∧ acceleratedOrbit 15 7051 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7051) = 3 ^ 10 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7051.1, data_15_7051.2]

/-- Complete interval computation for depth 15, residue 7052. -/
theorem bounds_15_7052 : exactInterval 15 7052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7052 : oddCount 7052 15 = 6 ∧ acceleratedOrbit 15 7052 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7052) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7052.1, data_15_7052.2]

/-- Complete interval computation for depth 15, residue 7053. -/
theorem bounds_15_7053 : exactInterval 15 7053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7053 : oddCount 7053 15 = 6 ∧ acceleratedOrbit 15 7053 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7053) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7053.1, data_15_7053.2]

/-- Complete interval computation for depth 15, residue 7054. -/
theorem bounds_15_7054 : exactInterval 15 7054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7054 : oddCount 7054 15 = 6 ∧ acceleratedOrbit 15 7054 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7054) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7054.1, data_15_7054.2]

/-- Complete interval computation for depth 15, residue 7055. -/
theorem bounds_15_7055 : exactInterval 15 7055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7055 : oddCount 7055 15 = 6 ∧ acceleratedOrbit 15 7055 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7055) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7055.1, data_15_7055.2]

/-- Complete interval computation for depth 15, residue 7056. -/
theorem bounds_15_7056 : exactInterval 15 7056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7056 : oddCount 7056 15 = 5 ∧ acceleratedOrbit 15 7056 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7056) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7056.1, data_15_7056.2]

/-- Complete interval computation for depth 15, residue 7057. -/
theorem bounds_15_7057 : exactInterval 15 7057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7057 : oddCount 7057 15 = 7 ∧ acceleratedOrbit 15 7057 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7057) = 3 ^ 7 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7057.1, data_15_7057.2]

/-- Complete interval computation for depth 15, residue 7058. -/
theorem bounds_15_7058 : exactInterval 15 7058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7058 : oddCount 7058 15 = 7 ∧ acceleratedOrbit 15 7058 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7058) = 3 ^ 7 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7058.1, data_15_7058.2]

/-- Complete interval computation for depth 15, residue 7059. -/
theorem bounds_15_7059 : exactInterval 15 7059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7059 : oddCount 7059 15 = 7 ∧ acceleratedOrbit 15 7059 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7059) = 3 ^ 7 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7059.1, data_15_7059.2]

/-- Complete interval computation for depth 15, residue 7060. -/
theorem bounds_15_7060 : exactInterval 15 7060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7060 : oddCount 7060 15 = 5 ∧ acceleratedOrbit 15 7060 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7060) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7060.1, data_15_7060.2]

/-- Complete interval computation for depth 15, residue 7061. -/
theorem bounds_15_7061 : exactInterval 15 7061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7061 : oddCount 7061 15 = 5 ∧ acceleratedOrbit 15 7061 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7061) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7061.1, data_15_7061.2]

/-- Complete interval computation for depth 15, residue 7062. -/
theorem bounds_15_7062 : exactInterval 15 7062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7062 : oddCount 7062 15 = 8 ∧ acceleratedOrbit 15 7062 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7062) = 3 ^ 8 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7062.1, data_15_7062.2]

/-- Complete interval computation for depth 15, residue 7063. -/
theorem bounds_15_7063 : exactInterval 15 7063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7063 : oddCount 7063 15 = 8 ∧ acceleratedOrbit 15 7063 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7063) = 3 ^ 8 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7063.1, data_15_7063.2]

/-- Complete interval computation for depth 15, residue 7064. -/
theorem bounds_15_7064 : exactInterval 15 7064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7064 : oddCount 7064 15 = 5 ∧ acceleratedOrbit 15 7064 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7064) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7064.1, data_15_7064.2]

/-- Complete interval computation for depth 15, residue 7065. -/
theorem bounds_15_7065 : exactInterval 15 7065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7065 : oddCount 7065 15 = 8 ∧ acceleratedOrbit 15 7065 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7065) = 3 ^ 8 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7065.1, data_15_7065.2]

/-- Complete interval computation for depth 15, residue 7066. -/
theorem bounds_15_7066 : exactInterval 15 7066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7066 : oddCount 7066 15 = 5 ∧ acceleratedOrbit 15 7066 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7066) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7066.1, data_15_7066.2]

/-- Complete interval computation for depth 15, residue 7067. -/
theorem bounds_15_7067 : exactInterval 15 7067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7067 : oddCount 7067 15 = 7 ∧ acceleratedOrbit 15 7067 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7067) = 3 ^ 7 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7067.1, data_15_7067.2]

/-- Complete interval computation for depth 15, residue 7068. -/
theorem bounds_15_7068 : exactInterval 15 7068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7068 : oddCount 7068 15 = 9 ∧ acceleratedOrbit 15 7068 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7068) = 3 ^ 9 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7068.1, data_15_7068.2]

/-- Complete interval computation for depth 15, residue 7069. -/
theorem bounds_15_7069 : exactInterval 15 7069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7069 : oddCount 7069 15 = 9 ∧ acceleratedOrbit 15 7069 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7069) = 3 ^ 9 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7069.1, data_15_7069.2]

/-- Complete interval computation for depth 15, residue 7070. -/
theorem bounds_15_7070 : exactInterval 15 7070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7070 : oddCount 7070 15 = 9 ∧ acceleratedOrbit 15 7070 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7070) = 3 ^ 9 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7070.1, data_15_7070.2]

/-- Complete interval computation for depth 15, residue 7071. -/
theorem bounds_15_7071 : exactInterval 15 7071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7071 : oddCount 7071 15 = 7 ∧ acceleratedOrbit 15 7071 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7071) = 3 ^ 7 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7071.1, data_15_7071.2]

/-- Complete interval computation for depth 15, residue 7072. -/
theorem bounds_15_7072 : exactInterval 15 7072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7072 : oddCount 7072 15 = 6 ∧ acceleratedOrbit 15 7072 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7072) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7072.1, data_15_7072.2]

/-- Complete interval computation for depth 15, residue 7073. -/
theorem bounds_15_7073 : exactInterval 15 7073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7073 : oddCount 7073 15 = 9 ∧ acceleratedOrbit 15 7073 = 4252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7073) = 3 ^ 9 * m + 4252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7073.1, data_15_7073.2]

/-- Complete interval computation for depth 15, residue 7074. -/
theorem bounds_15_7074 : exactInterval 15 7074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7074 : oddCount 7074 15 = 5 ∧ acceleratedOrbit 15 7074 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7074) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7074.1, data_15_7074.2]

/-- Complete interval computation for depth 15, residue 7075. -/
theorem bounds_15_7075 : exactInterval 15 7075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7075 : oddCount 7075 15 = 5 ∧ acceleratedOrbit 15 7075 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7075) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7075.1, data_15_7075.2]

/-- Complete interval computation for depth 15, residue 7076. -/
theorem bounds_15_7076 : exactInterval 15 7076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7076 : oddCount 7076 15 = 9 ∧ acceleratedOrbit 15 7076 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7076) = 3 ^ 9 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7076.1, data_15_7076.2]

end Collatz.Research.PassageAtlas.Batch0216
