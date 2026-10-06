import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0857

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5980. -/
theorem bounds_13_5980 : exactInterval 13 5980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5980 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5980) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5980 : oddCount 5980 13 = 6 ∧ acceleratedOrbit 13 5980 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5980 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5980) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5980.1, data_13_5980.2]

/-- Complete interval computation for depth 13, residue 5981. -/
theorem bounds_13_5981 : exactInterval 13 5981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5981 : oddCount 5981 13 = 6 ∧ acceleratedOrbit 13 5981 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5981) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5981.1, data_13_5981.2]

/-- Complete interval computation for depth 13, residue 5982. -/
theorem bounds_13_5982 : exactInterval 13 5982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5982 : oddCount 5982 13 = 6 ∧ acceleratedOrbit 13 5982 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5982) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5982.1, data_13_5982.2]

/-- Complete interval computation for depth 13, residue 5983. -/
theorem bounds_13_5983 : exactInterval 13 5983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5983 : oddCount 5983 13 = 6 ∧ acceleratedOrbit 13 5983 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5983) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5983.1, data_13_5983.2]

/-- Complete interval computation for depth 13, residue 5984. -/
theorem bounds_13_5984 : exactInterval 13 5984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5984 : oddCount 5984 13 = 5 ∧ acceleratedOrbit 13 5984 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5984) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5984.1, data_13_5984.2]

/-- Complete interval computation for depth 13, residue 5985. -/
theorem bounds_13_5985 : exactInterval 13 5985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5985 : oddCount 5985 13 = 8 ∧ acceleratedOrbit 13 5985 = 4796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5985) = 3 ^ 8 * m + 4796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5985.1, data_13_5985.2]

/-- Complete interval computation for depth 13, residue 5986. -/
theorem bounds_13_5986 : exactInterval 13 5986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5986 : oddCount 5986 13 = 5 ∧ acceleratedOrbit 13 5986 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5986) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5986.1, data_13_5986.2]

/-- Complete interval computation for depth 13, residue 5987. -/
theorem bounds_13_5987 : exactInterval 13 5987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5987 : oddCount 5987 13 = 5 ∧ acceleratedOrbit 13 5987 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5987) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5987.1, data_13_5987.2]

/-- Complete interval computation for depth 13, residue 5988. -/
theorem bounds_13_5988 : exactInterval 13 5988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5988 : oddCount 5988 13 = 5 ∧ acceleratedOrbit 13 5988 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5988) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5988.1, data_13_5988.2]

/-- Complete interval computation for depth 13, residue 5989. -/
theorem bounds_13_5989 : exactInterval 13 5989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5989 : oddCount 5989 13 = 5 ∧ acceleratedOrbit 13 5989 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5989) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5989.1, data_13_5989.2]

/-- Complete interval computation for depth 13, residue 5990. -/
theorem bounds_13_5990 : exactInterval 13 5990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5990 : oddCount 5990 13 = 5 ∧ acceleratedOrbit 13 5990 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5990) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5990.1, data_13_5990.2]

/-- Complete interval computation for depth 13, residue 5991. -/
theorem bounds_13_5991 : exactInterval 13 5991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5991 : oddCount 5991 13 = 10 ∧ acceleratedOrbit 13 5991 = 43193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5991) = 3 ^ 10 * m + 43193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5991.1, data_13_5991.2]

/-- Complete interval computation for depth 13, residue 5992. -/
theorem bounds_13_5992 : exactInterval 13 5992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5992 : oddCount 5992 13 = 5 ∧ acceleratedOrbit 13 5992 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5992) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5992.1, data_13_5992.2]

/-- Complete interval computation for depth 13, residue 5993. -/
theorem bounds_13_5993 : exactInterval 13 5993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5993 : oddCount 5993 13 = 7 ∧ acceleratedOrbit 13 5993 = 1601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5993) = 3 ^ 7 * m + 1601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5993.1, data_13_5993.2]

/-- Complete interval computation for depth 13, residue 5994. -/
theorem bounds_13_5994 : exactInterval 13 5994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5994 : oddCount 5994 13 = 5 ∧ acceleratedOrbit 13 5994 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5994) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5994.1, data_13_5994.2]

end Collatz.Research.StoppingAtlas.Batch0857
