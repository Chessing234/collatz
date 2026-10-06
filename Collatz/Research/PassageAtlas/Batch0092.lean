import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0092

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2981. -/
theorem bounds_15_2981 : exactInterval 15 2981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2981 : oddCount 2981 15 = 9 ∧ acceleratedOrbit 15 2981 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2981) = 3 ^ 9 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2981.1, data_15_2981.2]

/-- Complete interval computation for depth 15, residue 2982. -/
theorem bounds_15_2982 : exactInterval 15 2982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2982 : oddCount 2982 15 = 9 ∧ acceleratedOrbit 15 2982 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2982) = 3 ^ 9 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2982.1, data_15_2982.2]

/-- Complete interval computation for depth 15, residue 2983. -/
theorem bounds_15_2983 : exactInterval 15 2983 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2983) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2983 : oddCount 2983 15 = 9 ∧ acceleratedOrbit 15 2983 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2983) = 3 ^ 9 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2983.1, data_15_2983.2]

/-- Complete interval computation for depth 15, residue 2984. -/
theorem bounds_15_2984 : exactInterval 15 2984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2984 : oddCount 2984 15 = 4 ∧ acceleratedOrbit 15 2984 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2984) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2984.1, data_15_2984.2]

/-- Complete interval computation for depth 15, residue 2985. -/
theorem bounds_15_2985 : exactInterval 15 2985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2985 : oddCount 2985 15 = 8 ∧ acceleratedOrbit 15 2985 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2985) = 3 ^ 8 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2985.1, data_15_2985.2]

/-- Complete interval computation for depth 15, residue 2986. -/
theorem bounds_15_2986 : exactInterval 15 2986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2986 : oddCount 2986 15 = 4 ∧ acceleratedOrbit 15 2986 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2986) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2986.1, data_15_2986.2]

/-- Complete interval computation for depth 15, residue 2987. -/
theorem bounds_15_2987 : exactInterval 15 2987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2987 : oddCount 2987 15 = 7 ∧ acceleratedOrbit 15 2987 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2987) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2987.1, data_15_2987.2]

/-- Complete interval computation for depth 15, residue 2988. -/
theorem bounds_15_2988 : exactInterval 15 2988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2988 : oddCount 2988 15 = 7 ∧ acceleratedOrbit 15 2988 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2988) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2988.1, data_15_2988.2]

/-- Complete interval computation for depth 15, residue 2989. -/
theorem bounds_15_2989 : exactInterval 15 2989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2989 : oddCount 2989 15 = 7 ∧ acceleratedOrbit 15 2989 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2989) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2989.1, data_15_2989.2]

/-- Complete interval computation for depth 15, residue 2990. -/
theorem bounds_15_2990 : exactInterval 15 2990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2990 : oddCount 2990 15 = 7 ∧ acceleratedOrbit 15 2990 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2990) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2990.1, data_15_2990.2]

/-- Complete interval computation for depth 15, residue 2991. -/
theorem bounds_15_2991 : exactInterval 15 2991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2991 : oddCount 2991 15 = 7 ∧ acceleratedOrbit 15 2991 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2991) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2991.1, data_15_2991.2]

/-- Complete interval computation for depth 15, residue 2992. -/
theorem bounds_15_2992 : exactInterval 15 2992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2992 : oddCount 2992 15 = 7 ∧ acceleratedOrbit 15 2992 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2992) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2992.1, data_15_2992.2]

/-- Complete interval computation for depth 15, residue 2993. -/
theorem bounds_15_2993 : exactInterval 15 2993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2993 : oddCount 2993 15 = 7 ∧ acceleratedOrbit 15 2993 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2993) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2993.1, data_15_2993.2]

/-- Complete interval computation for depth 15, residue 2994. -/
theorem bounds_15_2994 : exactInterval 15 2994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2994 : oddCount 2994 15 = 7 ∧ acceleratedOrbit 15 2994 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2994) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2994.1, data_15_2994.2]

/-- Complete interval computation for depth 15, residue 2995. -/
theorem bounds_15_2995 : exactInterval 15 2995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2995 : oddCount 2995 15 = 7 ∧ acceleratedOrbit 15 2995 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2995) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2995.1, data_15_2995.2]

/-- Complete interval computation for depth 15, residue 2996. -/
theorem bounds_15_2996 : exactInterval 15 2996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2996 : oddCount 2996 15 = 7 ∧ acceleratedOrbit 15 2996 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2996) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2996.1, data_15_2996.2]

/-- Complete interval computation for depth 15, residue 2997. -/
theorem bounds_15_2997 : exactInterval 15 2997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2997 : oddCount 2997 15 = 7 ∧ acceleratedOrbit 15 2997 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2997) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2997.1, data_15_2997.2]

/-- Complete interval computation for depth 15, residue 2998. -/
theorem bounds_15_2998 : exactInterval 15 2998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2998 : oddCount 2998 15 = 6 ∧ acceleratedOrbit 15 2998 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2998) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2998.1, data_15_2998.2]

/-- Complete interval computation for depth 15, residue 2999. -/
theorem bounds_15_2999 : exactInterval 15 2999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2999 : oddCount 2999 15 = 6 ∧ acceleratedOrbit 15 2999 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2999) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2999.1, data_15_2999.2]

/-- Complete interval computation for depth 15, residue 3000. -/
theorem bounds_15_3000 : exactInterval 15 3000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3000 : oddCount 3000 15 = 7 ∧ acceleratedOrbit 15 3000 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3000) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3000.1, data_15_3000.2]

/-- Complete interval computation for depth 15, residue 3001. -/
theorem bounds_15_3001 : exactInterval 15 3001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3001 : oddCount 3001 15 = 9 ∧ acceleratedOrbit 15 3001 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3001) = 3 ^ 9 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3001.1, data_15_3001.2]

/-- Complete interval computation for depth 15, residue 3002. -/
theorem bounds_15_3002 : exactInterval 15 3002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3002 : oddCount 3002 15 = 7 ∧ acceleratedOrbit 15 3002 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3002) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3002.1, data_15_3002.2]

/-- Complete interval computation for depth 15, residue 3003. -/
theorem bounds_15_3003 : exactInterval 15 3003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3003 : oddCount 3003 15 = 9 ∧ acceleratedOrbit 15 3003 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3003) = 3 ^ 9 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3003.1, data_15_3003.2]

/-- Complete interval computation for depth 15, residue 3004. -/
theorem bounds_15_3004 : exactInterval 15 3004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3004 : oddCount 3004 15 = 10 ∧ acceleratedOrbit 15 3004 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3004) = 3 ^ 10 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3004.1, data_15_3004.2]

/-- Complete interval computation for depth 15, residue 3005. -/
theorem bounds_15_3005 : exactInterval 15 3005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3005 : oddCount 3005 15 = 10 ∧ acceleratedOrbit 15 3005 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3005) = 3 ^ 10 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3005.1, data_15_3005.2]

/-- Complete interval computation for depth 15, residue 3006. -/
theorem bounds_15_3006 : exactInterval 15 3006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3006 : oddCount 3006 15 = 10 ∧ acceleratedOrbit 15 3006 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3006) = 3 ^ 10 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3006.1, data_15_3006.2]

/-- Complete interval computation for depth 15, residue 3007. -/
theorem bounds_15_3007 : exactInterval 15 3007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3007 : oddCount 3007 15 = 12 ∧ acceleratedOrbit 15 3007 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3007) = 3 ^ 12 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3007.1, data_15_3007.2]

/-- Complete interval computation for depth 15, residue 3008. -/
theorem bounds_15_3008 : exactInterval 15 3008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3008 : oddCount 3008 15 = 7 ∧ acceleratedOrbit 15 3008 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3008) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3008.1, data_15_3008.2]

/-- Complete interval computation for depth 15, residue 3009. -/
theorem bounds_15_3009 : exactInterval 15 3009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3009 : oddCount 3009 15 = 8 ∧ acceleratedOrbit 15 3009 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3009) = 3 ^ 8 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3009.1, data_15_3009.2]

/-- Complete interval computation for depth 15, residue 3010. -/
theorem bounds_15_3010 : exactInterval 15 3010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3010 : oddCount 3010 15 = 8 ∧ acceleratedOrbit 15 3010 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3010) = 3 ^ 8 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3010.1, data_15_3010.2]

/-- Complete interval computation for depth 15, residue 3011. -/
theorem bounds_15_3011 : exactInterval 15 3011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3011 : oddCount 3011 15 = 8 ∧ acceleratedOrbit 15 3011 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3011) = 3 ^ 8 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3011.1, data_15_3011.2]

/-- Complete interval computation for depth 15, residue 3012. -/
theorem bounds_15_3012 : exactInterval 15 3012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3012 : oddCount 3012 15 = 4 ∧ acceleratedOrbit 15 3012 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3012) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3012.1, data_15_3012.2]

/-- Complete interval computation for depth 15, residue 3013. -/
theorem bounds_15_3013 : exactInterval 15 3013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3013 : oddCount 3013 15 = 4 ∧ acceleratedOrbit 15 3013 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3013) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3013.1, data_15_3013.2]

end Collatz.Research.PassageAtlas.Batch0092
