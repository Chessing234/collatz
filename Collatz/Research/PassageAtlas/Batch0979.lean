import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0979

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32047. -/
theorem bounds_15_32047 : exactInterval 15 32047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32047 : oddCount 32047 15 = 12 ∧ acceleratedOrbit 15 32047 = 519776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32047) = 3 ^ 12 * m + 519776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32047.1, data_15_32047.2]

/-- Complete interval computation for depth 15, residue 32048. -/
theorem bounds_15_32048 : exactInterval 15 32048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32048 : oddCount 32048 15 = 8 ∧ acceleratedOrbit 15 32048 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32048) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32048.1, data_15_32048.2]

/-- Complete interval computation for depth 15, residue 32049. -/
theorem bounds_15_32049 : exactInterval 15 32049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32049 : oddCount 32049 15 = 8 ∧ acceleratedOrbit 15 32049 = 6419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32049) = 3 ^ 8 * m + 6419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32049.1, data_15_32049.2]

/-- Complete interval computation for depth 15, residue 32050. -/
theorem bounds_15_32050 : exactInterval 15 32050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32050 : oddCount 32050 15 = 8 ∧ acceleratedOrbit 15 32050 = 6419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32050) = 3 ^ 8 * m + 6419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32050.1, data_15_32050.2]

/-- Complete interval computation for depth 15, residue 32051. -/
theorem bounds_15_32051 : exactInterval 15 32051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32051 : oddCount 32051 15 = 8 ∧ acceleratedOrbit 15 32051 = 6419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32051) = 3 ^ 8 * m + 6419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32051.1, data_15_32051.2]

/-- Complete interval computation for depth 15, residue 32052. -/
theorem bounds_15_32052 : exactInterval 15 32052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32052 : oddCount 32052 15 = 8 ∧ acceleratedOrbit 15 32052 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32052) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32052.1, data_15_32052.2]

/-- Complete interval computation for depth 15, residue 32053. -/
theorem bounds_15_32053 : exactInterval 15 32053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32053 : oddCount 32053 15 = 8 ∧ acceleratedOrbit 15 32053 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32053) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32053.1, data_15_32053.2]

/-- Complete interval computation for depth 15, residue 32054. -/
theorem bounds_15_32054 : exactInterval 15 32054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32054 : oddCount 32054 15 = 9 ∧ acceleratedOrbit 15 32054 = 19256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32054) = 3 ^ 9 * m + 19256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32054.1, data_15_32054.2]

/-- Complete interval computation for depth 15, residue 32055. -/
theorem bounds_15_32055 : exactInterval 15 32055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32055 : oddCount 32055 15 = 9 ∧ acceleratedOrbit 15 32055 = 19256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32055) = 3 ^ 9 * m + 19256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32055.1, data_15_32055.2]

/-- Complete interval computation for depth 15, residue 32056. -/
theorem bounds_15_32056 : exactInterval 15 32056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32056 : oddCount 32056 15 = 8 ∧ acceleratedOrbit 15 32056 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32056) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32056.1, data_15_32056.2]

/-- Complete interval computation for depth 15, residue 32057. -/
theorem bounds_15_32057 : exactInterval 15 32057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32057 : oddCount 32057 15 = 10 ∧ acceleratedOrbit 15 32057 = 57773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32057) = 3 ^ 10 * m + 57773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32057.1, data_15_32057.2]

/-- Complete interval computation for depth 15, residue 32058. -/
theorem bounds_15_32058 : exactInterval 15 32058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32058 : oddCount 32058 15 = 8 ∧ acceleratedOrbit 15 32058 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32058) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32058.1, data_15_32058.2]

/-- Complete interval computation for depth 15, residue 32059. -/
theorem bounds_15_32059 : exactInterval 15 32059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32059 : oddCount 32059 15 = 5 ∧ acceleratedOrbit 15 32059 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32059) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32059.1, data_15_32059.2]

/-- Complete interval computation for depth 15, residue 32060. -/
theorem bounds_15_32060 : exactInterval 15 32060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32060 : oddCount 32060 15 = 8 ∧ acceleratedOrbit 15 32060 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32060) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32060.1, data_15_32060.2]

/-- Complete interval computation for depth 15, residue 32061. -/
theorem bounds_15_32061 : exactInterval 15 32061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32061 : oddCount 32061 15 = 8 ∧ acceleratedOrbit 15 32061 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32061) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32061.1, data_15_32061.2]

/-- Complete interval computation for depth 15, residue 32062. -/
theorem bounds_15_32062 : exactInterval 15 32062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32062 : oddCount 32062 15 = 10 ∧ acceleratedOrbit 15 32062 = 57781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32062) = 3 ^ 10 * m + 57781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32062.1, data_15_32062.2]

/-- Complete interval computation for depth 15, residue 32063. -/
theorem bounds_15_32063 : exactInterval 15 32063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32063 : oddCount 32063 15 = 10 ∧ acceleratedOrbit 15 32063 = 57781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32063) = 3 ^ 10 * m + 57781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32063.1, data_15_32063.2]

/-- Complete interval computation for depth 15, residue 32064. -/
theorem bounds_15_32064 : exactInterval 15 32064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32064 : oddCount 32064 15 = 5 ∧ acceleratedOrbit 15 32064 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32064) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32064.1, data_15_32064.2]

/-- Complete interval computation for depth 15, residue 32065. -/
theorem bounds_15_32065 : exactInterval 15 32065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32065 : oddCount 32065 15 = 8 ∧ acceleratedOrbit 15 32065 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32065) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32065.1, data_15_32065.2]

/-- Complete interval computation for depth 15, residue 32066. -/
theorem bounds_15_32066 : exactInterval 15 32066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32066 : oddCount 32066 15 = 7 ∧ acceleratedOrbit 15 32066 = 2141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32066) = 3 ^ 7 * m + 2141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32066.1, data_15_32066.2]

/-- Complete interval computation for depth 15, residue 32067. -/
theorem bounds_15_32067 : exactInterval 15 32067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32067 : oddCount 32067 15 = 7 ∧ acceleratedOrbit 15 32067 = 2141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32067) = 3 ^ 7 * m + 2141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32067.1, data_15_32067.2]

/-- Complete interval computation for depth 15, residue 32068. -/
theorem bounds_15_32068 : exactInterval 15 32068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32068 : oddCount 32068 15 = 8 ∧ acceleratedOrbit 15 32068 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32068) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32068.1, data_15_32068.2]

/-- Complete interval computation for depth 15, residue 32069. -/
theorem bounds_15_32069 : exactInterval 15 32069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32069 : oddCount 32069 15 = 8 ∧ acceleratedOrbit 15 32069 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32069) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32069.1, data_15_32069.2]

/-- Complete interval computation for depth 15, residue 32070. -/
theorem bounds_15_32070 : exactInterval 15 32070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32070 : oddCount 32070 15 = 8 ∧ acceleratedOrbit 15 32070 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32070) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32070.1, data_15_32070.2]

/-- Complete interval computation for depth 15, residue 32071. -/
theorem bounds_15_32071 : exactInterval 15 32071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32071 : oddCount 32071 15 = 10 ∧ acceleratedOrbit 15 32071 = 57797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32071) = 3 ^ 10 * m + 57797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32071.1, data_15_32071.2]

/-- Complete interval computation for depth 15, residue 32072. -/
theorem bounds_15_32072 : exactInterval 15 32072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32072 : oddCount 32072 15 = 9 ∧ acceleratedOrbit 15 32072 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32072) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32072.1, data_15_32072.2]

/-- Complete interval computation for depth 15, residue 32073. -/
theorem bounds_15_32073 : exactInterval 15 32073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32073 : oddCount 32073 15 = 9 ∧ acceleratedOrbit 15 32073 = 19268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32073) = 3 ^ 9 * m + 19268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32073.1, data_15_32073.2]

/-- Complete interval computation for depth 15, residue 32074. -/
theorem bounds_15_32074 : exactInterval 15 32074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32074 : oddCount 32074 15 = 9 ∧ acceleratedOrbit 15 32074 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32074) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32074.1, data_15_32074.2]

/-- Complete interval computation for depth 15, residue 32075. -/
theorem bounds_15_32075 : exactInterval 15 32075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32075 : oddCount 32075 15 = 8 ∧ acceleratedOrbit 15 32075 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32075) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32075.1, data_15_32075.2]

/-- Complete interval computation for depth 15, residue 32076. -/
theorem bounds_15_32076 : exactInterval 15 32076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32076 : oddCount 32076 15 = 9 ∧ acceleratedOrbit 15 32076 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32076) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32076.1, data_15_32076.2]

/-- Complete interval computation for depth 15, residue 32077. -/
theorem bounds_15_32077 : exactInterval 15 32077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32077 : oddCount 32077 15 = 9 ∧ acceleratedOrbit 15 32077 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32077) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32077.1, data_15_32077.2]

/-- Complete interval computation for depth 15, residue 32078. -/
theorem bounds_15_32078 : exactInterval 15 32078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32078 : oddCount 32078 15 = 9 ∧ acceleratedOrbit 15 32078 = 19271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32078) = 3 ^ 9 * m + 19271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32078.1, data_15_32078.2]

end Collatz.Research.PassageAtlas.Batch0979
