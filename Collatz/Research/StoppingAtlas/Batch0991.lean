import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0991

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8038. -/
theorem bounds_13_8038 : exactInterval 13 8038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8038 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8038) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8038 : oddCount 8038 13 = 4 ∧ acceleratedOrbit 13 8038 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8038 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8038) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8038.1, data_13_8038.2]

/-- Complete interval computation for depth 13, residue 8039. -/
theorem bounds_13_8039 : exactInterval 13 8039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8039 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8039) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8039 : oddCount 8039 13 = 11 ∧ acceleratedOrbit 13 8039 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8039 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8039) = 3 ^ 11 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8039.1, data_13_8039.2]

/-- Complete interval computation for depth 13, residue 8040. -/
theorem bounds_13_8040 : exactInterval 13 8040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8040 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8040) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8040 : oddCount 8040 13 = 6 ∧ acceleratedOrbit 13 8040 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8040 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8040) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8040.1, data_13_8040.2]

/-- Complete interval computation for depth 13, residue 8041. -/
theorem bounds_13_8041 : exactInterval 13 8041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8041 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8041) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8041 : oddCount 8041 13 = 8 ∧ acceleratedOrbit 13 8041 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8041 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8041) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8041.1, data_13_8041.2]

/-- Complete interval computation for depth 13, residue 8042. -/
theorem bounds_13_8042 : exactInterval 13 8042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8042 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8042) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8042 : oddCount 8042 13 = 6 ∧ acceleratedOrbit 13 8042 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8042 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8042) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8042.1, data_13_8042.2]

/-- Complete interval computation for depth 13, residue 8043. -/
theorem bounds_13_8043 : exactInterval 13 8043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8043 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8043) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8043 : oddCount 8043 13 = 6 ∧ acceleratedOrbit 13 8043 = 716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8043 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8043) = 3 ^ 6 * m + 716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8043.1, data_13_8043.2]

/-- Complete interval computation for depth 13, residue 8044. -/
theorem bounds_13_8044 : exactInterval 13 8044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8044 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8044) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8044 : oddCount 8044 13 = 7 ∧ acceleratedOrbit 13 8044 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8044 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8044) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8044.1, data_13_8044.2]

/-- Complete interval computation for depth 13, residue 8045. -/
theorem bounds_13_8045 : exactInterval 13 8045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8045 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8045) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8045 : oddCount 8045 13 = 7 ∧ acceleratedOrbit 13 8045 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8045 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8045) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8045.1, data_13_8045.2]

/-- Complete interval computation for depth 13, residue 8046. -/
theorem bounds_13_8046 : exactInterval 13 8046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8046 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8046) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8046 : oddCount 8046 13 = 7 ∧ acceleratedOrbit 13 8046 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8046 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8046) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8046.1, data_13_8046.2]

/-- Complete interval computation for depth 13, residue 8047. -/
theorem bounds_13_8047 : exactInterval 13 8047 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8047 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8047) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8047 : oddCount 8047 13 = 8 ∧ acceleratedOrbit 13 8047 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8047 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8047) = 3 ^ 8 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8047.1, data_13_8047.2]

/-- Complete interval computation for depth 13, residue 8048. -/
theorem bounds_13_8048 : exactInterval 13 8048 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8048 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8048) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8048 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8048 : oddCount 8048 13 = 6 ∧ acceleratedOrbit 13 8048 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8048 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8048) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8048.1, data_13_8048.2]

/-- Complete interval computation for depth 13, residue 8049. -/
theorem bounds_13_8049 : exactInterval 13 8049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8049 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8049) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8049 : oddCount 8049 13 = 6 ∧ acceleratedOrbit 13 8049 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8049 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8049) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8049.1, data_13_8049.2]

/-- Complete interval computation for depth 13, residue 8050. -/
theorem bounds_13_8050 : exactInterval 13 8050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8050 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8050) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8050 : oddCount 8050 13 = 5 ∧ acceleratedOrbit 13 8050 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8050 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8050) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8050.1, data_13_8050.2]

/-- Complete interval computation for depth 13, residue 8051. -/
theorem bounds_13_8051 : exactInterval 13 8051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8051 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8051) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8051 : oddCount 8051 13 = 5 ∧ acceleratedOrbit 13 8051 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8051 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8051) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8051.1, data_13_8051.2]

/-- Complete interval computation for depth 13, residue 8052. -/
theorem bounds_13_8052 : exactInterval 13 8052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8052 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8052) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8052 : oddCount 8052 13 = 6 ∧ acceleratedOrbit 13 8052 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8052 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8052) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8052.1, data_13_8052.2]

end Collatz.Research.StoppingAtlas.Batch0991
