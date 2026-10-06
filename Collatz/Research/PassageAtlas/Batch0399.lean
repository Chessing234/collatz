import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0399

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13041. -/
theorem bounds_15_13041 : exactInterval 15 13041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13041 : oddCount 13041 15 = 5 ∧ acceleratedOrbit 15 13041 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13041) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13041.1, data_15_13041.2]

/-- Complete interval computation for depth 15, residue 13042. -/
theorem bounds_15_13042 : exactInterval 15 13042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13042 : oddCount 13042 15 = 10 ∧ acceleratedOrbit 15 13042 = 23510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13042) = 3 ^ 10 * m + 23510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13042.1, data_15_13042.2]

/-- Complete interval computation for depth 15, residue 13043. -/
theorem bounds_15_13043 : exactInterval 15 13043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13043 : oddCount 13043 15 = 10 ∧ acceleratedOrbit 15 13043 = 23510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13043) = 3 ^ 10 * m + 23510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13043.1, data_15_13043.2]

/-- Complete interval computation for depth 15, residue 13044. -/
theorem bounds_15_13044 : exactInterval 15 13044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13044 : oddCount 13044 15 = 7 ∧ acceleratedOrbit 15 13044 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13044) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13044.1, data_15_13044.2]

/-- Complete interval computation for depth 15, residue 13045. -/
theorem bounds_15_13045 : exactInterval 15 13045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13045 : oddCount 13045 15 = 7 ∧ acceleratedOrbit 15 13045 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13045) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13045.1, data_15_13045.2]

/-- Complete interval computation for depth 15, residue 13046. -/
theorem bounds_15_13046 : exactInterval 15 13046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13046 : oddCount 13046 15 = 7 ∧ acceleratedOrbit 15 13046 = 871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13046) = 3 ^ 7 * m + 871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13046.1, data_15_13046.2]

/-- Complete interval computation for depth 15, residue 13047. -/
theorem bounds_15_13047 : exactInterval 15 13047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13047 : oddCount 13047 15 = 7 ∧ acceleratedOrbit 15 13047 = 871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13047) = 3 ^ 7 * m + 871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13047.1, data_15_13047.2]

/-- Complete interval computation for depth 15, residue 13048. -/
theorem bounds_15_13048 : exactInterval 15 13048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13048 : oddCount 13048 15 = 7 ∧ acceleratedOrbit 15 13048 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13048) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13048.1, data_15_13048.2]

/-- Complete interval computation for depth 15, residue 13049. -/
theorem bounds_15_13049 : exactInterval 15 13049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13049 : oddCount 13049 15 = 8 ∧ acceleratedOrbit 15 13049 = 2614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13049) = 3 ^ 8 * m + 2614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13049.1, data_15_13049.2]

/-- Complete interval computation for depth 15, residue 13050. -/
theorem bounds_15_13050 : exactInterval 15 13050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13050 : oddCount 13050 15 = 7 ∧ acceleratedOrbit 15 13050 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13050) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13050.1, data_15_13050.2]

/-- Complete interval computation for depth 15, residue 13051. -/
theorem bounds_15_13051 : exactInterval 15 13051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13051 : oddCount 13051 15 = 9 ∧ acceleratedOrbit 15 13051 = 7841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13051) = 3 ^ 9 * m + 7841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13051.1, data_15_13051.2]

/-- Complete interval computation for depth 15, residue 13052. -/
theorem bounds_15_13052 : exactInterval 15 13052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13052 : oddCount 13052 15 = 9 ∧ acceleratedOrbit 15 13052 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13052) = 3 ^ 9 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13052.1, data_15_13052.2]

/-- Complete interval computation for depth 15, residue 13053. -/
theorem bounds_15_13053 : exactInterval 15 13053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13053 : oddCount 13053 15 = 9 ∧ acceleratedOrbit 15 13053 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13053) = 3 ^ 9 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13053.1, data_15_13053.2]

/-- Complete interval computation for depth 15, residue 13054. -/
theorem bounds_15_13054 : exactInterval 15 13054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13054 : oddCount 13054 15 = 9 ∧ acceleratedOrbit 15 13054 = 7843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13054) = 3 ^ 9 * m + 7843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13054.1, data_15_13054.2]

/-- Complete interval computation for depth 15, residue 13055. -/
theorem bounds_15_13055 : exactInterval 15 13055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13055 : oddCount 13055 15 = 12 ∧ acceleratedOrbit 15 13055 = 211747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13055) = 3 ^ 12 * m + 211747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13055.1, data_15_13055.2]

/-- Complete interval computation for depth 15, residue 13056. -/
theorem bounds_15_13056 : exactInterval 15 13056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13056 : oddCount 13056 15 = 3 ∧ acceleratedOrbit 15 13056 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13056) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13056.1, data_15_13056.2]

/-- Complete interval computation for depth 15, residue 13057. -/
theorem bounds_15_13057 : exactInterval 15 13057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13057 : oddCount 13057 15 = 8 ∧ acceleratedOrbit 15 13057 = 2618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13057) = 3 ^ 8 * m + 2618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13057.1, data_15_13057.2]

/-- Complete interval computation for depth 15, residue 13058. -/
theorem bounds_15_13058 : exactInterval 15 13058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13058 : oddCount 13058 15 = 8 ∧ acceleratedOrbit 15 13058 = 2618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13058) = 3 ^ 8 * m + 2618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13058.1, data_15_13058.2]

/-- Complete interval computation for depth 15, residue 13059. -/
theorem bounds_15_13059 : exactInterval 15 13059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13059 : oddCount 13059 15 = 8 ∧ acceleratedOrbit 15 13059 = 2618 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13059) = 3 ^ 8 * m + 2618 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13059.1, data_15_13059.2]

/-- Complete interval computation for depth 15, residue 13060. -/
theorem bounds_15_13060 : exactInterval 15 13060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13060 : oddCount 13060 15 = 5 ∧ acceleratedOrbit 15 13060 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13060) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13060.1, data_15_13060.2]

/-- Complete interval computation for depth 15, residue 13061. -/
theorem bounds_15_13061 : exactInterval 15 13061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13061 : oddCount 13061 15 = 5 ∧ acceleratedOrbit 15 13061 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13061) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13061.1, data_15_13061.2]

/-- Complete interval computation for depth 15, residue 13062. -/
theorem bounds_15_13062 : exactInterval 15 13062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13062 : oddCount 13062 15 = 5 ∧ acceleratedOrbit 15 13062 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13062) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13062.1, data_15_13062.2]

/-- Complete interval computation for depth 15, residue 13063. -/
theorem bounds_15_13063 : exactInterval 15 13063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13063 : oddCount 13063 15 = 7 ∧ acceleratedOrbit 15 13063 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13063) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13063.1, data_15_13063.2]

/-- Complete interval computation for depth 15, residue 13064. -/
theorem bounds_15_13064 : exactInterval 15 13064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13064 : oddCount 13064 15 = 5 ∧ acceleratedOrbit 15 13064 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13064) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13064.1, data_15_13064.2]

/-- Complete interval computation for depth 15, residue 13065. -/
theorem bounds_15_13065 : exactInterval 15 13065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13065 : oddCount 13065 15 = 9 ∧ acceleratedOrbit 15 13065 = 7850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13065) = 3 ^ 9 * m + 7850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13065.1, data_15_13065.2]

/-- Complete interval computation for depth 15, residue 13066. -/
theorem bounds_15_13066 : exactInterval 15 13066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13066 : oddCount 13066 15 = 5 ∧ acceleratedOrbit 15 13066 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13066) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13066.1, data_15_13066.2]

/-- Complete interval computation for depth 15, residue 13067. -/
theorem bounds_15_13067 : exactInterval 15 13067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13067 : oddCount 13067 15 = 9 ∧ acceleratedOrbit 15 13067 = 7852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13067) = 3 ^ 9 * m + 7852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13067.1, data_15_13067.2]

/-- Complete interval computation for depth 15, residue 13068. -/
theorem bounds_15_13068 : exactInterval 15 13068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13068 : oddCount 13068 15 = 5 ∧ acceleratedOrbit 15 13068 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13068) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13068.1, data_15_13068.2]

/-- Complete interval computation for depth 15, residue 13069. -/
theorem bounds_15_13069 : exactInterval 15 13069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13069 : oddCount 13069 15 = 5 ∧ acceleratedOrbit 15 13069 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13069) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13069.1, data_15_13069.2]

/-- Complete interval computation for depth 15, residue 13070. -/
theorem bounds_15_13070 : exactInterval 15 13070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13070 : oddCount 13070 15 = 5 ∧ acceleratedOrbit 15 13070 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13070) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13070.1, data_15_13070.2]

/-- Complete interval computation for depth 15, residue 13071. -/
theorem bounds_15_13071 : exactInterval 15 13071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13071 : oddCount 13071 15 = 5 ∧ acceleratedOrbit 15 13071 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13071) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13071.1, data_15_13071.2]

/-- Complete interval computation for depth 15, residue 13072. -/
theorem bounds_15_13072 : exactInterval 15 13072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13072 : oddCount 13072 15 = 5 ∧ acceleratedOrbit 15 13072 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13072) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13072.1, data_15_13072.2]

/-- Complete interval computation for depth 15, residue 13073. -/
theorem bounds_15_13073 : exactInterval 15 13073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13073 : oddCount 13073 15 = 5 ∧ acceleratedOrbit 15 13073 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13073) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13073.1, data_15_13073.2]

end Collatz.Research.PassageAtlas.Batch0399
