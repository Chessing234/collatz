import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0826

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27033. -/
theorem bounds_15_27033 : exactInterval 15 27033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27033 : oddCount 27033 15 = 6 ∧ acceleratedOrbit 15 27033 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27033) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27033.1, data_15_27033.2]

/-- Complete interval computation for depth 15, residue 27034. -/
theorem bounds_15_27034 : exactInterval 15 27034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27034 : oddCount 27034 15 = 7 ∧ acceleratedOrbit 15 27034 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27034) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27034.1, data_15_27034.2]

/-- Complete interval computation for depth 15, residue 27035. -/
theorem bounds_15_27035 : exactInterval 15 27035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27035 : oddCount 27035 15 = 11 ∧ acceleratedOrbit 15 27035 = 146164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27035) = 3 ^ 11 * m + 146164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27035.1, data_15_27035.2]

/-- Complete interval computation for depth 15, residue 27036. -/
theorem bounds_15_27036 : exactInterval 15 27036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27036 : oddCount 27036 15 = 9 ∧ acceleratedOrbit 15 27036 = 16244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27036) = 3 ^ 9 * m + 16244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27036.1, data_15_27036.2]

/-- Complete interval computation for depth 15, residue 27037. -/
theorem bounds_15_27037 : exactInterval 15 27037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27037 : oddCount 27037 15 = 9 ∧ acceleratedOrbit 15 27037 = 16244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27037) = 3 ^ 9 * m + 16244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27037.1, data_15_27037.2]

/-- Complete interval computation for depth 15, residue 27038. -/
theorem bounds_15_27038 : exactInterval 15 27038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27038 : oddCount 27038 15 = 9 ∧ acceleratedOrbit 15 27038 = 16244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27038) = 3 ^ 9 * m + 16244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27038.1, data_15_27038.2]

/-- Complete interval computation for depth 15, residue 27039. -/
theorem bounds_15_27039 : exactInterval 15 27039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27039 : oddCount 27039 15 = 10 ∧ acceleratedOrbit 15 27039 = 48728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27039) = 3 ^ 10 * m + 48728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27039.1, data_15_27039.2]

/-- Complete interval computation for depth 15, residue 27040. -/
theorem bounds_15_27040 : exactInterval 15 27040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27040 : oddCount 27040 15 = 5 ∧ acceleratedOrbit 15 27040 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27040) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27040.1, data_15_27040.2]

/-- Complete interval computation for depth 15, residue 27041. -/
theorem bounds_15_27041 : exactInterval 15 27041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27041 : oddCount 27041 15 = 7 ∧ acceleratedOrbit 15 27041 = 1805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27041) = 3 ^ 7 * m + 1805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27041.1, data_15_27041.2]

/-- Complete interval computation for depth 15, residue 27042. -/
theorem bounds_15_27042 : exactInterval 15 27042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27042 : oddCount 27042 15 = 8 ∧ acceleratedOrbit 15 27042 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27042) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27042.1, data_15_27042.2]

/-- Complete interval computation for depth 15, residue 27043. -/
theorem bounds_15_27043 : exactInterval 15 27043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27043 : oddCount 27043 15 = 8 ∧ acceleratedOrbit 15 27043 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27043) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27043.1, data_15_27043.2]

/-- Complete interval computation for depth 15, residue 27044. -/
theorem bounds_15_27044 : exactInterval 15 27044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27044 : oddCount 27044 15 = 8 ∧ acceleratedOrbit 15 27044 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27044) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27044.1, data_15_27044.2]

/-- Complete interval computation for depth 15, residue 27045. -/
theorem bounds_15_27045 : exactInterval 15 27045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27045 : oddCount 27045 15 = 8 ∧ acceleratedOrbit 15 27045 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27045) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27045.1, data_15_27045.2]

/-- Complete interval computation for depth 15, residue 27046. -/
theorem bounds_15_27046 : exactInterval 15 27046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27046 : oddCount 27046 15 = 8 ∧ acceleratedOrbit 15 27046 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27046) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27046.1, data_15_27046.2]

/-- Complete interval computation for depth 15, residue 27047. -/
theorem bounds_15_27047 : exactInterval 15 27047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27047 : oddCount 27047 15 = 8 ∧ acceleratedOrbit 15 27047 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27047) = 3 ^ 8 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27047.1, data_15_27047.2]

/-- Complete interval computation for depth 15, residue 27048. -/
theorem bounds_15_27048 : exactInterval 15 27048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27048 : oddCount 27048 15 = 5 ∧ acceleratedOrbit 15 27048 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27048) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27048.1, data_15_27048.2]

/-- Complete interval computation for depth 15, residue 27049. -/
theorem bounds_15_27049 : exactInterval 15 27049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27049 : oddCount 27049 15 = 9 ∧ acceleratedOrbit 15 27049 = 16249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27049) = 3 ^ 9 * m + 16249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27049.1, data_15_27049.2]

/-- Complete interval computation for depth 15, residue 27050. -/
theorem bounds_15_27050 : exactInterval 15 27050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27050 : oddCount 27050 15 = 5 ∧ acceleratedOrbit 15 27050 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27050) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27050.1, data_15_27050.2]

/-- Complete interval computation for depth 15, residue 27051. -/
theorem bounds_15_27051 : exactInterval 15 27051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27051 : oddCount 27051 15 = 10 ∧ acceleratedOrbit 15 27051 = 48752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27051) = 3 ^ 10 * m + 48752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27051.1, data_15_27051.2]

/-- Complete interval computation for depth 15, residue 27052. -/
theorem bounds_15_27052 : exactInterval 15 27052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27052 : oddCount 27052 15 = 6 ∧ acceleratedOrbit 15 27052 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27052) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27052.1, data_15_27052.2]

/-- Complete interval computation for depth 15, residue 27053. -/
theorem bounds_15_27053 : exactInterval 15 27053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27053 : oddCount 27053 15 = 6 ∧ acceleratedOrbit 15 27053 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27053) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27053.1, data_15_27053.2]

/-- Complete interval computation for depth 15, residue 27054. -/
theorem bounds_15_27054 : exactInterval 15 27054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27054 : oddCount 27054 15 = 6 ∧ acceleratedOrbit 15 27054 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27054) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27054.1, data_15_27054.2]

/-- Complete interval computation for depth 15, residue 27055. -/
theorem bounds_15_27055 : exactInterval 15 27055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27055 : oddCount 27055 15 = 10 ∧ acceleratedOrbit 15 27055 = 48761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27055) = 3 ^ 10 * m + 48761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27055.1, data_15_27055.2]

/-- Complete interval computation for depth 15, residue 27056. -/
theorem bounds_15_27056 : exactInterval 15 27056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27056 : oddCount 27056 15 = 8 ∧ acceleratedOrbit 15 27056 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27056) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27056.1, data_15_27056.2]

/-- Complete interval computation for depth 15, residue 27057. -/
theorem bounds_15_27057 : exactInterval 15 27057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27057 : oddCount 27057 15 = 7 ∧ acceleratedOrbit 15 27057 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27057) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27057.1, data_15_27057.2]

/-- Complete interval computation for depth 15, residue 27058. -/
theorem bounds_15_27058 : exactInterval 15 27058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27058 : oddCount 27058 15 = 7 ∧ acceleratedOrbit 15 27058 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27058) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27058.1, data_15_27058.2]

/-- Complete interval computation for depth 15, residue 27059. -/
theorem bounds_15_27059 : exactInterval 15 27059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27059 : oddCount 27059 15 = 7 ∧ acceleratedOrbit 15 27059 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27059) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27059.1, data_15_27059.2]

/-- Complete interval computation for depth 15, residue 27060. -/
theorem bounds_15_27060 : exactInterval 15 27060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27060 : oddCount 27060 15 = 8 ∧ acceleratedOrbit 15 27060 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27060) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27060.1, data_15_27060.2]

/-- Complete interval computation for depth 15, residue 27061. -/
theorem bounds_15_27061 : exactInterval 15 27061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27061 : oddCount 27061 15 = 8 ∧ acceleratedOrbit 15 27061 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27061) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27061.1, data_15_27061.2]

/-- Complete interval computation for depth 15, residue 27062. -/
theorem bounds_15_27062 : exactInterval 15 27062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27062 : oddCount 27062 15 = 8 ∧ acceleratedOrbit 15 27062 = 5420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27062) = 3 ^ 8 * m + 5420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27062.1, data_15_27062.2]

/-- Complete interval computation for depth 15, residue 27063. -/
theorem bounds_15_27063 : exactInterval 15 27063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27063 : oddCount 27063 15 = 8 ∧ acceleratedOrbit 15 27063 = 5420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27063) = 3 ^ 8 * m + 5420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27063.1, data_15_27063.2]

/-- Complete interval computation for depth 15, residue 27064. -/
theorem bounds_15_27064 : exactInterval 15 27064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27064 : oddCount 27064 15 = 8 ∧ acceleratedOrbit 15 27064 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27064) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27064.1, data_15_27064.2]

/-- Complete interval computation for depth 15, residue 27065. -/
theorem bounds_15_27065 : exactInterval 15 27065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27065 : oddCount 27065 15 = 7 ∧ acceleratedOrbit 15 27065 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27065) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27065.1, data_15_27065.2]

end Collatz.Research.PassageAtlas.Batch0826
