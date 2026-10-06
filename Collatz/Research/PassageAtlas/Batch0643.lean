import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0643

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21037. -/
theorem bounds_15_21037 : exactInterval 15 21037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21037 : oddCount 21037 15 = 7 ∧ acceleratedOrbit 15 21037 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21037) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21037.1, data_15_21037.2]

/-- Complete interval computation for depth 15, residue 21038. -/
theorem bounds_15_21038 : exactInterval 15 21038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21038 : oddCount 21038 15 = 7 ∧ acceleratedOrbit 15 21038 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21038) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21038.1, data_15_21038.2]

/-- Complete interval computation for depth 15, residue 21039. -/
theorem bounds_15_21039 : exactInterval 15 21039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21039 : oddCount 21039 15 = 10 ∧ acceleratedOrbit 15 21039 = 37916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21039) = 3 ^ 10 * m + 37916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21039.1, data_15_21039.2]

/-- Complete interval computation for depth 15, residue 21040. -/
theorem bounds_15_21040 : exactInterval 15 21040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21040 : oddCount 21040 15 = 5 ∧ acceleratedOrbit 15 21040 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21040) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21040.1, data_15_21040.2]

/-- Complete interval computation for depth 15, residue 21041. -/
theorem bounds_15_21041 : exactInterval 15 21041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21041 : oddCount 21041 15 = 7 ∧ acceleratedOrbit 15 21041 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21041) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21041.1, data_15_21041.2]

/-- Complete interval computation for depth 15, residue 21042. -/
theorem bounds_15_21042 : exactInterval 15 21042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21042 : oddCount 21042 15 = 7 ∧ acceleratedOrbit 15 21042 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21042) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21042.1, data_15_21042.2]

/-- Complete interval computation for depth 15, residue 21043. -/
theorem bounds_15_21043 : exactInterval 15 21043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21043 : oddCount 21043 15 = 7 ∧ acceleratedOrbit 15 21043 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21043) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21043.1, data_15_21043.2]

/-- Complete interval computation for depth 15, residue 21044. -/
theorem bounds_15_21044 : exactInterval 15 21044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21044 : oddCount 21044 15 = 5 ∧ acceleratedOrbit 15 21044 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21044) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21044.1, data_15_21044.2]

/-- Complete interval computation for depth 15, residue 21045. -/
theorem bounds_15_21045 : exactInterval 15 21045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21045 : oddCount 21045 15 = 5 ∧ acceleratedOrbit 15 21045 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21045) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21045.1, data_15_21045.2]

/-- Complete interval computation for depth 15, residue 21046. -/
theorem bounds_15_21046 : exactInterval 15 21046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21046 : oddCount 21046 15 = 9 ∧ acceleratedOrbit 15 21046 = 12644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21046) = 3 ^ 9 * m + 12644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21046.1, data_15_21046.2]

/-- Complete interval computation for depth 15, residue 21047. -/
theorem bounds_15_21047 : exactInterval 15 21047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21047 : oddCount 21047 15 = 9 ∧ acceleratedOrbit 15 21047 = 12644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21047) = 3 ^ 9 * m + 12644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21047.1, data_15_21047.2]

/-- Complete interval computation for depth 15, residue 21048. -/
theorem bounds_15_21048 : exactInterval 15 21048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21048 : oddCount 21048 15 = 7 ∧ acceleratedOrbit 15 21048 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21048) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21048.1, data_15_21048.2]

/-- Complete interval computation for depth 15, residue 21049. -/
theorem bounds_15_21049 : exactInterval 15 21049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21049 : oddCount 21049 15 = 9 ∧ acceleratedOrbit 15 21049 = 12646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21049) = 3 ^ 9 * m + 12646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21049.1, data_15_21049.2]

/-- Complete interval computation for depth 15, residue 21050. -/
theorem bounds_15_21050 : exactInterval 15 21050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21050 : oddCount 21050 15 = 7 ∧ acceleratedOrbit 15 21050 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21050) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21050.1, data_15_21050.2]

/-- Complete interval computation for depth 15, residue 21051. -/
theorem bounds_15_21051 : exactInterval 15 21051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21051 : oddCount 21051 15 = 7 ∧ acceleratedOrbit 15 21051 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21051) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21051.1, data_15_21051.2]

/-- Complete interval computation for depth 15, residue 21052. -/
theorem bounds_15_21052 : exactInterval 15 21052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21052 : oddCount 21052 15 = 7 ∧ acceleratedOrbit 15 21052 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21052) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21052.1, data_15_21052.2]

/-- Complete interval computation for depth 15, residue 21053. -/
theorem bounds_15_21053 : exactInterval 15 21053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21053 : oddCount 21053 15 = 7 ∧ acceleratedOrbit 15 21053 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21053) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21053.1, data_15_21053.2]

/-- Complete interval computation for depth 15, residue 21054. -/
theorem bounds_15_21054 : exactInterval 15 21054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21054 : oddCount 21054 15 = 9 ∧ acceleratedOrbit 15 21054 = 12649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21054) = 3 ^ 9 * m + 12649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21054.1, data_15_21054.2]

/-- Complete interval computation for depth 15, residue 21055. -/
theorem bounds_15_21055 : exactInterval 15 21055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21055 : oddCount 21055 15 = 9 ∧ acceleratedOrbit 15 21055 = 12649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21055) = 3 ^ 9 * m + 12649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21055.1, data_15_21055.2]

/-- Complete interval computation for depth 15, residue 21056. -/
theorem bounds_15_21056 : exactInterval 15 21056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21056 : oddCount 21056 15 = 5 ∧ acceleratedOrbit 15 21056 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21056) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21056.1, data_15_21056.2]

/-- Complete interval computation for depth 15, residue 21057. -/
theorem bounds_15_21057 : exactInterval 15 21057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21057 : oddCount 21057 15 = 6 ∧ acceleratedOrbit 15 21057 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21057) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21057.1, data_15_21057.2]

/-- Complete interval computation for depth 15, residue 21058. -/
theorem bounds_15_21058 : exactInterval 15 21058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21058 : oddCount 21058 15 = 6 ∧ acceleratedOrbit 15 21058 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21058) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21058.1, data_15_21058.2]

/-- Complete interval computation for depth 15, residue 21059. -/
theorem bounds_15_21059 : exactInterval 15 21059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21059 : oddCount 21059 15 = 6 ∧ acceleratedOrbit 15 21059 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21059) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21059.1, data_15_21059.2]

/-- Complete interval computation for depth 15, residue 21060. -/
theorem bounds_15_21060 : exactInterval 15 21060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21060 : oddCount 21060 15 = 6 ∧ acceleratedOrbit 15 21060 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21060) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21060.1, data_15_21060.2]

/-- Complete interval computation for depth 15, residue 21061. -/
theorem bounds_15_21061 : exactInterval 15 21061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21061 : oddCount 21061 15 = 6 ∧ acceleratedOrbit 15 21061 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21061) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21061.1, data_15_21061.2]

/-- Complete interval computation for depth 15, residue 21062. -/
theorem bounds_15_21062 : exactInterval 15 21062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21062 : oddCount 21062 15 = 6 ∧ acceleratedOrbit 15 21062 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21062) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21062.1, data_15_21062.2]

/-- Complete interval computation for depth 15, residue 21063. -/
theorem bounds_15_21063 : exactInterval 15 21063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21063 : oddCount 21063 15 = 7 ∧ acceleratedOrbit 15 21063 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21063) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21063.1, data_15_21063.2]

/-- Complete interval computation for depth 15, residue 21064. -/
theorem bounds_15_21064 : exactInterval 15 21064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21064 : oddCount 21064 15 = 6 ∧ acceleratedOrbit 15 21064 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21064) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21064.1, data_15_21064.2]

/-- Complete interval computation for depth 15, residue 21065. -/
theorem bounds_15_21065 : exactInterval 15 21065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21065 : oddCount 21065 15 = 9 ∧ acceleratedOrbit 15 21065 = 12656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21065) = 3 ^ 9 * m + 12656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21065.1, data_15_21065.2]

/-- Complete interval computation for depth 15, residue 21066. -/
theorem bounds_15_21066 : exactInterval 15 21066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21066 : oddCount 21066 15 = 6 ∧ acceleratedOrbit 15 21066 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21066) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21066.1, data_15_21066.2]

/-- Complete interval computation for depth 15, residue 21067. -/
theorem bounds_15_21067 : exactInterval 15 21067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21067 : oddCount 21067 15 = 6 ∧ acceleratedOrbit 15 21067 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21067) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21067.1, data_15_21067.2]

/-- Complete interval computation for depth 15, residue 21068. -/
theorem bounds_15_21068 : exactInterval 15 21068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21068 : oddCount 21068 15 = 6 ∧ acceleratedOrbit 15 21068 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21068) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21068.1, data_15_21068.2]

end Collatz.Research.PassageAtlas.Batch0643
