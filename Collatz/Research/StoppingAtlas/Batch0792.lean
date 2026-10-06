import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0792

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4981. -/
theorem bounds_13_4981 : exactInterval 13 4981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4981 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4981) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4981 : oddCount 4981 13 = 6 ∧ acceleratedOrbit 13 4981 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4981 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4981) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4981.1, data_13_4981.2]

/-- Complete interval computation for depth 13, residue 4982. -/
theorem bounds_13_4982 : exactInterval 13 4982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4982 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4982) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4982 : oddCount 4982 13 = 8 ∧ acceleratedOrbit 13 4982 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4982 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4982) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4982.1, data_13_4982.2]

/-- Complete interval computation for depth 13, residue 4983. -/
theorem bounds_13_4983 : exactInterval 13 4983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4983 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4983) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4983 : oddCount 4983 13 = 8 ∧ acceleratedOrbit 13 4983 = 3995 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4983 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4983) = 3 ^ 8 * m + 3995 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4983.1, data_13_4983.2]

/-- Complete interval computation for depth 13, residue 4984. -/
theorem bounds_13_4984 : exactInterval 13 4984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4984 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4984) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4984 : oddCount 4984 13 = 7 ∧ acceleratedOrbit 13 4984 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4984 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4984) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4984.1, data_13_4984.2]

/-- Complete interval computation for depth 13, residue 4985. -/
theorem bounds_13_4985 : exactInterval 13 4985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4985 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4985) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4985 : oddCount 4985 13 = 9 ∧ acceleratedOrbit 13 4985 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4985 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4985) = 3 ^ 9 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4985.1, data_13_4985.2]

/-- Complete interval computation for depth 13, residue 4986. -/
theorem bounds_13_4986 : exactInterval 13 4986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4986 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4986) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4986 : oddCount 4986 13 = 7 ∧ acceleratedOrbit 13 4986 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4986 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4986) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4986.1, data_13_4986.2]

/-- Complete interval computation for depth 13, residue 4987. -/
theorem bounds_13_4987 : exactInterval 13 4987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4987 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4987) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4987 : oddCount 4987 13 = 10 ∧ acceleratedOrbit 13 4987 = 35963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4987 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4987) = 3 ^ 10 * m + 35963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4987.1, data_13_4987.2]

/-- Complete interval computation for depth 13, residue 4988. -/
theorem bounds_13_4988 : exactInterval 13 4988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4988 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4988) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4988 : oddCount 4988 13 = 7 ∧ acceleratedOrbit 13 4988 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4988 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4988) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4988.1, data_13_4988.2]

/-- Complete interval computation for depth 13, residue 4989. -/
theorem bounds_13_4989 : exactInterval 13 4989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4989 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4989) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4989 : oddCount 4989 13 = 7 ∧ acceleratedOrbit 13 4989 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4989 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4989) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4989.1, data_13_4989.2]

/-- Complete interval computation for depth 13, residue 4990. -/
theorem bounds_13_4990 : exactInterval 13 4990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4990 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4990) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4990 : oddCount 4990 13 = 10 ∧ acceleratedOrbit 13 4990 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4990 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4990) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4990.1, data_13_4990.2]

/-- Complete interval computation for depth 13, residue 4991. -/
theorem bounds_13_4991 : exactInterval 13 4991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4991 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4991) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4991 : oddCount 4991 13 = 10 ∧ acceleratedOrbit 13 4991 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4991 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4991) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4991.1, data_13_4991.2]

/-- Complete interval computation for depth 13, residue 4992. -/
theorem bounds_13_4992 : exactInterval 13 4992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4992 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4992) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4992 : oddCount 4992 13 = 5 ∧ acceleratedOrbit 13 4992 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4992 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4992) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4992.1, data_13_4992.2]

/-- Complete interval computation for depth 13, residue 4993. -/
theorem bounds_13_4993 : exactInterval 13 4993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4993 : oddCount 4993 13 = 7 ∧ acceleratedOrbit 13 4993 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4993) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4993.1, data_13_4993.2]

/-- Complete interval computation for depth 13, residue 4994. -/
theorem bounds_13_4994 : exactInterval 13 4994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4994 : oddCount 4994 13 = 7 ∧ acceleratedOrbit 13 4994 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4994) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4994.1, data_13_4994.2]

/-- Complete interval computation for depth 13, residue 4995. -/
theorem bounds_13_4995 : exactInterval 13 4995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4995 : oddCount 4995 13 = 7 ∧ acceleratedOrbit 13 4995 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4995) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4995.1, data_13_4995.2]

/-- Complete interval computation for depth 13, residue 4996. -/
theorem bounds_13_4996 : exactInterval 13 4996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4996 : oddCount 4996 13 = 8 ∧ acceleratedOrbit 13 4996 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4996) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4996.1, data_13_4996.2]

end Collatz.Research.StoppingAtlas.Batch0792
