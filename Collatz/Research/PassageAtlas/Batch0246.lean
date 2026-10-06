import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0246

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8028. -/
theorem bounds_15_8028 : exactInterval 15 8028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8028 : oddCount 8028 15 = 8 ∧ acceleratedOrbit 15 8028 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8028) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8028.1, data_15_8028.2]

/-- Complete interval computation for depth 15, residue 8029. -/
theorem bounds_15_8029 : exactInterval 15 8029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8029 : oddCount 8029 15 = 8 ∧ acceleratedOrbit 15 8029 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8029) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8029.1, data_15_8029.2]

/-- Complete interval computation for depth 15, residue 8030. -/
theorem bounds_15_8030 : exactInterval 15 8030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8030 : oddCount 8030 15 = 8 ∧ acceleratedOrbit 15 8030 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8030) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8030.1, data_15_8030.2]

/-- Complete interval computation for depth 15, residue 8031. -/
theorem bounds_15_8031 : exactInterval 15 8031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8031 : oddCount 8031 15 = 8 ∧ acceleratedOrbit 15 8031 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8031) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8031.1, data_15_8031.2]

/-- Complete interval computation for depth 15, residue 8032. -/
theorem bounds_15_8032 : exactInterval 15 8032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8032 : oddCount 8032 15 = 8 ∧ acceleratedOrbit 15 8032 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8032) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8032.1, data_15_8032.2]

/-- Complete interval computation for depth 15, residue 8033. -/
theorem bounds_15_8033 : exactInterval 15 8033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8033 : oddCount 8033 15 = 8 ∧ acceleratedOrbit 15 8033 = 1609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8033) = 3 ^ 8 * m + 1609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8033.1, data_15_8033.2]

/-- Complete interval computation for depth 15, residue 8034. -/
theorem bounds_15_8034 : exactInterval 15 8034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8034 : oddCount 8034 15 = 4 ∧ acceleratedOrbit 15 8034 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8034) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8034.1, data_15_8034.2]

/-- Complete interval computation for depth 15, residue 8035. -/
theorem bounds_15_8035 : exactInterval 15 8035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8035 : oddCount 8035 15 = 4 ∧ acceleratedOrbit 15 8035 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8035) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8035.1, data_15_8035.2]

/-- Complete interval computation for depth 15, residue 8036. -/
theorem bounds_15_8036 : exactInterval 15 8036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8036 : oddCount 8036 15 = 4 ∧ acceleratedOrbit 15 8036 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8036) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8036.1, data_15_8036.2]

/-- Complete interval computation for depth 15, residue 8037. -/
theorem bounds_15_8037 : exactInterval 15 8037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8037 : oddCount 8037 15 = 4 ∧ acceleratedOrbit 15 8037 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8037) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8037.1, data_15_8037.2]

/-- Complete interval computation for depth 15, residue 8038. -/
theorem bounds_15_8038 : exactInterval 15 8038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8038 : oddCount 8038 15 = 4 ∧ acceleratedOrbit 15 8038 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8038) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8038.1, data_15_8038.2]

/-- Complete interval computation for depth 15, residue 8039. -/
theorem bounds_15_8039 : exactInterval 15 8039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8039 : oddCount 8039 15 = 12 ∧ acceleratedOrbit 15 8039 = 130400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8039) = 3 ^ 12 * m + 130400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8039.1, data_15_8039.2]

/-- Complete interval computation for depth 15, residue 8040. -/
theorem bounds_15_8040 : exactInterval 15 8040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8040 : oddCount 8040 15 = 8 ∧ acceleratedOrbit 15 8040 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8040) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8040.1, data_15_8040.2]

/-- Complete interval computation for depth 15, residue 8041. -/
theorem bounds_15_8041 : exactInterval 15 8041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8041 : oddCount 8041 15 = 10 ∧ acceleratedOrbit 15 8041 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8041) = 3 ^ 10 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8041.1, data_15_8041.2]

/-- Complete interval computation for depth 15, residue 8042. -/
theorem bounds_15_8042 : exactInterval 15 8042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8042 : oddCount 8042 15 = 8 ∧ acceleratedOrbit 15 8042 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8042) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8042.1, data_15_8042.2]

/-- Complete interval computation for depth 15, residue 8043. -/
theorem bounds_15_8043 : exactInterval 15 8043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8043 : oddCount 8043 15 = 6 ∧ acceleratedOrbit 15 8043 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8043) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8043.1, data_15_8043.2]

/-- Complete interval computation for depth 15, residue 8044. -/
theorem bounds_15_8044 : exactInterval 15 8044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8044 : oddCount 8044 15 = 8 ∧ acceleratedOrbit 15 8044 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8044) = 3 ^ 8 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8044.1, data_15_8044.2]

/-- Complete interval computation for depth 15, residue 8045. -/
theorem bounds_15_8045 : exactInterval 15 8045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8045 : oddCount 8045 15 = 8 ∧ acceleratedOrbit 15 8045 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8045) = 3 ^ 8 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8045.1, data_15_8045.2]

/-- Complete interval computation for depth 15, residue 8046. -/
theorem bounds_15_8046 : exactInterval 15 8046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8046 : oddCount 8046 15 = 8 ∧ acceleratedOrbit 15 8046 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8046) = 3 ^ 8 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8046.1, data_15_8046.2]

/-- Complete interval computation for depth 15, residue 8047. -/
theorem bounds_15_8047 : exactInterval 15 8047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8047 : oddCount 8047 15 = 9 ∧ acceleratedOrbit 15 8047 = 4835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8047) = 3 ^ 9 * m + 4835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8047.1, data_15_8047.2]

/-- Complete interval computation for depth 15, residue 8048. -/
theorem bounds_15_8048 : exactInterval 15 8048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8048 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8048) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8048 : oddCount 8048 15 = 8 ∧ acceleratedOrbit 15 8048 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8048 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8048) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8048.1, data_15_8048.2]

/-- Complete interval computation for depth 15, residue 8049. -/
theorem bounds_15_8049 : exactInterval 15 8049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8049 : oddCount 8049 15 = 8 ∧ acceleratedOrbit 15 8049 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8049) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8049.1, data_15_8049.2]

/-- Complete interval computation for depth 15, residue 8050. -/
theorem bounds_15_8050 : exactInterval 15 8050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8050 : oddCount 8050 15 = 7 ∧ acceleratedOrbit 15 8050 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8050) = 3 ^ 7 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8050.1, data_15_8050.2]

/-- Complete interval computation for depth 15, residue 8051. -/
theorem bounds_15_8051 : exactInterval 15 8051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8051 : oddCount 8051 15 = 7 ∧ acceleratedOrbit 15 8051 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8051) = 3 ^ 7 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8051.1, data_15_8051.2]

/-- Complete interval computation for depth 15, residue 8052. -/
theorem bounds_15_8052 : exactInterval 15 8052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8052 : oddCount 8052 15 = 8 ∧ acceleratedOrbit 15 8052 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8052) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8052.1, data_15_8052.2]

/-- Complete interval computation for depth 15, residue 8053. -/
theorem bounds_15_8053 : exactInterval 15 8053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8053 : oddCount 8053 15 = 8 ∧ acceleratedOrbit 15 8053 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8053) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8053.1, data_15_8053.2]

/-- Complete interval computation for depth 15, residue 8054. -/
theorem bounds_15_8054 : exactInterval 15 8054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8054 : oddCount 8054 15 = 7 ∧ acceleratedOrbit 15 8054 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8054) = 3 ^ 7 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8054.1, data_15_8054.2]

/-- Complete interval computation for depth 15, residue 8055. -/
theorem bounds_15_8055 : exactInterval 15 8055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8055 : oddCount 8055 15 = 7 ∧ acceleratedOrbit 15 8055 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8055) = 3 ^ 7 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8055.1, data_15_8055.2]

/-- Complete interval computation for depth 15, residue 8056. -/
theorem bounds_15_8056 : exactInterval 15 8056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8056 : oddCount 8056 15 = 8 ∧ acceleratedOrbit 15 8056 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8056) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8056.1, data_15_8056.2]

/-- Complete interval computation for depth 15, residue 8057. -/
theorem bounds_15_8057 : exactInterval 15 8057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8057 : oddCount 8057 15 = 10 ∧ acceleratedOrbit 15 8057 = 14525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8057) = 3 ^ 10 * m + 14525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8057.1, data_15_8057.2]

/-- Complete interval computation for depth 15, residue 8058. -/
theorem bounds_15_8058 : exactInterval 15 8058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8058 : oddCount 8058 15 = 8 ∧ acceleratedOrbit 15 8058 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8058) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8058.1, data_15_8058.2]

/-- Complete interval computation for depth 15, residue 8059. -/
theorem bounds_15_8059 : exactInterval 15 8059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8059 : oddCount 8059 15 = 7 ∧ acceleratedOrbit 15 8059 = 538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8059) = 3 ^ 7 * m + 538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8059.1, data_15_8059.2]

end Collatz.Research.PassageAtlas.Batch0246
