import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0277

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9043. -/
theorem bounds_15_9043 : exactInterval 15 9043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9043 : oddCount 9043 15 = 10 ∧ acceleratedOrbit 15 9043 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9043) = 3 ^ 10 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9043.1, data_15_9043.2]

/-- Complete interval computation for depth 15, residue 9044. -/
theorem bounds_15_9044 : exactInterval 15 9044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9044 : oddCount 9044 15 = 3 ∧ acceleratedOrbit 15 9044 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9044) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9044.1, data_15_9044.2]

/-- Complete interval computation for depth 15, residue 9045. -/
theorem bounds_15_9045 : exactInterval 15 9045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9045 : oddCount 9045 15 = 3 ∧ acceleratedOrbit 15 9045 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9045) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9045.1, data_15_9045.2]

/-- Complete interval computation for depth 15, residue 9046. -/
theorem bounds_15_9046 : exactInterval 15 9046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9046 : oddCount 9046 15 = 9 ∧ acceleratedOrbit 15 9046 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9046) = 3 ^ 9 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9046.1, data_15_9046.2]

/-- Complete interval computation for depth 15, residue 9047. -/
theorem bounds_15_9047 : exactInterval 15 9047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9047 : oddCount 9047 15 = 9 ∧ acceleratedOrbit 15 9047 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9047) = 3 ^ 9 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9047.1, data_15_9047.2]

/-- Complete interval computation for depth 15, residue 9048. -/
theorem bounds_15_9048 : exactInterval 15 9048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9048 : oddCount 9048 15 = 7 ∧ acceleratedOrbit 15 9048 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9048) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9048.1, data_15_9048.2]

/-- Complete interval computation for depth 15, residue 9049. -/
theorem bounds_15_9049 : exactInterval 15 9049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9049 : oddCount 9049 15 = 6 ∧ acceleratedOrbit 15 9049 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9049) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9049.1, data_15_9049.2]

/-- Complete interval computation for depth 15, residue 9050. -/
theorem bounds_15_9050 : exactInterval 15 9050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9050 : oddCount 9050 15 = 7 ∧ acceleratedOrbit 15 9050 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9050) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9050.1, data_15_9050.2]

/-- Complete interval computation for depth 15, residue 9051. -/
theorem bounds_15_9051 : exactInterval 15 9051 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9051) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9051 : oddCount 9051 15 = 9 ∧ acceleratedOrbit 15 9051 = 5438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9051) = 3 ^ 9 * m + 5438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9051.1, data_15_9051.2]

/-- Complete interval computation for depth 15, residue 9052. -/
theorem bounds_15_9052 : exactInterval 15 9052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9052 : oddCount 9052 15 = 7 ∧ acceleratedOrbit 15 9052 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9052) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9052.1, data_15_9052.2]

/-- Complete interval computation for depth 15, residue 9053. -/
theorem bounds_15_9053 : exactInterval 15 9053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9053 : oddCount 9053 15 = 7 ∧ acceleratedOrbit 15 9053 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9053) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9053.1, data_15_9053.2]

/-- Complete interval computation for depth 15, residue 9054. -/
theorem bounds_15_9054 : exactInterval 15 9054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9054 : oddCount 9054 15 = 7 ∧ acceleratedOrbit 15 9054 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9054) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9054.1, data_15_9054.2]

/-- Complete interval computation for depth 15, residue 9055. -/
theorem bounds_15_9055 : exactInterval 15 9055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9055 : oddCount 9055 15 = 7 ∧ acceleratedOrbit 15 9055 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9055) = 3 ^ 7 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9055.1, data_15_9055.2]

/-- Complete interval computation for depth 15, residue 9056. -/
theorem bounds_15_9056 : exactInterval 15 9056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9056 : oddCount 9056 15 = 8 ∧ acceleratedOrbit 15 9056 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9056) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9056.1, data_15_9056.2]

/-- Complete interval computation for depth 15, residue 9057. -/
theorem bounds_15_9057 : exactInterval 15 9057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9057 : oddCount 9057 15 = 8 ∧ acceleratedOrbit 15 9057 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9057) = 3 ^ 8 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9057.1, data_15_9057.2]

/-- Complete interval computation for depth 15, residue 9058. -/
theorem bounds_15_9058 : exactInterval 15 9058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9058 : oddCount 9058 15 = 7 ∧ acceleratedOrbit 15 9058 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9058) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9058.1, data_15_9058.2]

/-- Complete interval computation for depth 15, residue 9059. -/
theorem bounds_15_9059 : exactInterval 15 9059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9059 : oddCount 9059 15 = 7 ∧ acceleratedOrbit 15 9059 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9059) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9059.1, data_15_9059.2]

/-- Complete interval computation for depth 15, residue 9060. -/
theorem bounds_15_9060 : exactInterval 15 9060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9060 : oddCount 9060 15 = 7 ∧ acceleratedOrbit 15 9060 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9060) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9060.1, data_15_9060.2]

/-- Complete interval computation for depth 15, residue 9061. -/
theorem bounds_15_9061 : exactInterval 15 9061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9061 : oddCount 9061 15 = 7 ∧ acceleratedOrbit 15 9061 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9061) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9061.1, data_15_9061.2]

/-- Complete interval computation for depth 15, residue 9062. -/
theorem bounds_15_9062 : exactInterval 15 9062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9062 : oddCount 9062 15 = 7 ∧ acceleratedOrbit 15 9062 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9062) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9062.1, data_15_9062.2]

/-- Complete interval computation for depth 15, residue 9063. -/
theorem bounds_15_9063 : exactInterval 15 9063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9063 : oddCount 9063 15 = 12 ∧ acceleratedOrbit 15 9063 = 147008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9063) = 3 ^ 12 * m + 147008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9063.1, data_15_9063.2]

/-- Complete interval computation for depth 15, residue 9064. -/
theorem bounds_15_9064 : exactInterval 15 9064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9064 : oddCount 9064 15 = 8 ∧ acceleratedOrbit 15 9064 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9064) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9064.1, data_15_9064.2]

/-- Complete interval computation for depth 15, residue 9065. -/
theorem bounds_15_9065 : exactInterval 15 9065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9065 : oddCount 9065 15 = 9 ∧ acceleratedOrbit 15 9065 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9065) = 3 ^ 9 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9065.1, data_15_9065.2]

/-- Complete interval computation for depth 15, residue 9066. -/
theorem bounds_15_9066 : exactInterval 15 9066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9066 : oddCount 9066 15 = 8 ∧ acceleratedOrbit 15 9066 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9066) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9066.1, data_15_9066.2]

/-- Complete interval computation for depth 15, residue 9067. -/
theorem bounds_15_9067 : exactInterval 15 9067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9067 : oddCount 9067 15 = 6 ∧ acceleratedOrbit 15 9067 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9067) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9067.1, data_15_9067.2]

/-- Complete interval computation for depth 15, residue 9068. -/
theorem bounds_15_9068 : exactInterval 15 9068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9068 : oddCount 9068 15 = 9 ∧ acceleratedOrbit 15 9068 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9068) = 3 ^ 9 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9068.1, data_15_9068.2]

/-- Complete interval computation for depth 15, residue 9069. -/
theorem bounds_15_9069 : exactInterval 15 9069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9069 : oddCount 9069 15 = 9 ∧ acceleratedOrbit 15 9069 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9069) = 3 ^ 9 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9069.1, data_15_9069.2]

/-- Complete interval computation for depth 15, residue 9070. -/
theorem bounds_15_9070 : exactInterval 15 9070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9070 : oddCount 9070 15 = 9 ∧ acceleratedOrbit 15 9070 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9070) = 3 ^ 9 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9070.1, data_15_9070.2]

/-- Complete interval computation for depth 15, residue 9071. -/
theorem bounds_15_9071 : exactInterval 15 9071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9071 : oddCount 9071 15 = 8 ∧ acceleratedOrbit 15 9071 = 1817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9071) = 3 ^ 8 * m + 1817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9071.1, data_15_9071.2]

/-- Complete interval computation for depth 15, residue 9072. -/
theorem bounds_15_9072 : exactInterval 15 9072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9072 : oddCount 9072 15 = 8 ∧ acceleratedOrbit 15 9072 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9072) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9072.1, data_15_9072.2]

/-- Complete interval computation for depth 15, residue 9073. -/
theorem bounds_15_9073 : exactInterval 15 9073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9073 : oddCount 9073 15 = 8 ∧ acceleratedOrbit 15 9073 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9073) = 3 ^ 8 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9073.1, data_15_9073.2]

/-- Complete interval computation for depth 15, residue 9074. -/
theorem bounds_15_9074 : exactInterval 15 9074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9074 : oddCount 9074 15 = 7 ∧ acceleratedOrbit 15 9074 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9074) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9074.1, data_15_9074.2]

/-- Complete interval computation for depth 15, residue 9075. -/
theorem bounds_15_9075 : exactInterval 15 9075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9075 : oddCount 9075 15 = 7 ∧ acceleratedOrbit 15 9075 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9075) = 3 ^ 7 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9075.1, data_15_9075.2]

end Collatz.Research.PassageAtlas.Batch0277
