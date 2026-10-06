import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0308

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10059. -/
theorem bounds_15_10059 : exactInterval 15 10059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10059 : oddCount 10059 15 = 7 ∧ acceleratedOrbit 15 10059 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10059) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10059.1, data_15_10059.2]

/-- Complete interval computation for depth 15, residue 10060. -/
theorem bounds_15_10060 : exactInterval 15 10060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10060 : oddCount 10060 15 = 6 ∧ acceleratedOrbit 15 10060 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10060) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10060.1, data_15_10060.2]

/-- Complete interval computation for depth 15, residue 10061. -/
theorem bounds_15_10061 : exactInterval 15 10061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10061 : oddCount 10061 15 = 6 ∧ acceleratedOrbit 15 10061 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10061) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10061.1, data_15_10061.2]

/-- Complete interval computation for depth 15, residue 10062. -/
theorem bounds_15_10062 : exactInterval 15 10062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10062 : oddCount 10062 15 = 9 ∧ acceleratedOrbit 15 10062 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10062) = 3 ^ 9 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10062.1, data_15_10062.2]

/-- Complete interval computation for depth 15, residue 10063. -/
theorem bounds_15_10063 : exactInterval 15 10063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10063 : oddCount 10063 15 = 9 ∧ acceleratedOrbit 15 10063 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10063) = 3 ^ 9 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10063.1, data_15_10063.2]

/-- Complete interval computation for depth 15, residue 10064. -/
theorem bounds_15_10064 : exactInterval 15 10064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10064 : oddCount 10064 15 = 5 ∧ acceleratedOrbit 15 10064 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10064) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10064.1, data_15_10064.2]

/-- Complete interval computation for depth 15, residue 10065. -/
theorem bounds_15_10065 : exactInterval 15 10065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10065 : oddCount 10065 15 = 6 ∧ acceleratedOrbit 15 10065 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10065) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10065.1, data_15_10065.2]

/-- Complete interval computation for depth 15, residue 10066. -/
theorem bounds_15_10066 : exactInterval 15 10066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10066 : oddCount 10066 15 = 10 ∧ acceleratedOrbit 15 10066 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10066) = 3 ^ 10 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10066.1, data_15_10066.2]

/-- Complete interval computation for depth 15, residue 10067. -/
theorem bounds_15_10067 : exactInterval 15 10067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10067 : oddCount 10067 15 = 10 ∧ acceleratedOrbit 15 10067 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10067) = 3 ^ 10 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10067.1, data_15_10067.2]

/-- Complete interval computation for depth 15, residue 10068. -/
theorem bounds_15_10068 : exactInterval 15 10068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10068 : oddCount 10068 15 = 5 ∧ acceleratedOrbit 15 10068 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10068) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10068.1, data_15_10068.2]

/-- Complete interval computation for depth 15, residue 10069. -/
theorem bounds_15_10069 : exactInterval 15 10069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10069 : oddCount 10069 15 = 5 ∧ acceleratedOrbit 15 10069 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10069) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10069.1, data_15_10069.2]

/-- Complete interval computation for depth 15, residue 10070. -/
theorem bounds_15_10070 : exactInterval 15 10070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10070 : oddCount 10070 15 = 8 ∧ acceleratedOrbit 15 10070 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10070) = 3 ^ 8 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10070.1, data_15_10070.2]

/-- Complete interval computation for depth 15, residue 10071. -/
theorem bounds_15_10071 : exactInterval 15 10071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10071 : oddCount 10071 15 = 8 ∧ acceleratedOrbit 15 10071 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10071) = 3 ^ 8 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10071.1, data_15_10071.2]

/-- Complete interval computation for depth 15, residue 10072. -/
theorem bounds_15_10072 : exactInterval 15 10072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10072 : oddCount 10072 15 = 8 ∧ acceleratedOrbit 15 10072 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10072) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10072.1, data_15_10072.2]

/-- Complete interval computation for depth 15, residue 10073. -/
theorem bounds_15_10073 : exactInterval 15 10073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10073 : oddCount 10073 15 = 7 ∧ acceleratedOrbit 15 10073 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10073) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10073.1, data_15_10073.2]

/-- Complete interval computation for depth 15, residue 10074. -/
theorem bounds_15_10074 : exactInterval 15 10074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10074 : oddCount 10074 15 = 8 ∧ acceleratedOrbit 15 10074 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10074) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10074.1, data_15_10074.2]

/-- Complete interval computation for depth 15, residue 10075. -/
theorem bounds_15_10075 : exactInterval 15 10075 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10075) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10075 : oddCount 10075 15 = 9 ∧ acceleratedOrbit 15 10075 = 6053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10075) = 3 ^ 9 * m + 6053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10075.1, data_15_10075.2]

/-- Complete interval computation for depth 15, residue 10076. -/
theorem bounds_15_10076 : exactInterval 15 10076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10076 : oddCount 10076 15 = 8 ∧ acceleratedOrbit 15 10076 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10076) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10076.1, data_15_10076.2]

/-- Complete interval computation for depth 15, residue 10077. -/
theorem bounds_15_10077 : exactInterval 15 10077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10077 : oddCount 10077 15 = 8 ∧ acceleratedOrbit 15 10077 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10077) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10077.1, data_15_10077.2]

/-- Complete interval computation for depth 15, residue 10078. -/
theorem bounds_15_10078 : exactInterval 15 10078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10078 : oddCount 10078 15 = 7 ∧ acceleratedOrbit 15 10078 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10078) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10078.1, data_15_10078.2]

/-- Complete interval computation for depth 15, residue 10079. -/
theorem bounds_15_10079 : exactInterval 15 10079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10079 : oddCount 10079 15 = 7 ∧ acceleratedOrbit 15 10079 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10079) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10079.1, data_15_10079.2]

/-- Complete interval computation for depth 15, residue 10080. -/
theorem bounds_15_10080 : exactInterval 15 10080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10080 : oddCount 10080 15 = 4 ∧ acceleratedOrbit 15 10080 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10080) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10080.1, data_15_10080.2]

/-- Complete interval computation for depth 15, residue 10081. -/
theorem bounds_15_10081 : exactInterval 15 10081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10081 : oddCount 10081 15 = 7 ∧ acceleratedOrbit 15 10081 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10081) = 3 ^ 7 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10081.1, data_15_10081.2]

/-- Complete interval computation for depth 15, residue 10082. -/
theorem bounds_15_10082 : exactInterval 15 10082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10082 : oddCount 10082 15 = 4 ∧ acceleratedOrbit 15 10082 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10082) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10082.1, data_15_10082.2]

/-- Complete interval computation for depth 15, residue 10083. -/
theorem bounds_15_10083 : exactInterval 15 10083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10083 : oddCount 10083 15 = 4 ∧ acceleratedOrbit 15 10083 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10083) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10083.1, data_15_10083.2]

/-- Complete interval computation for depth 15, residue 10084. -/
theorem bounds_15_10084 : exactInterval 15 10084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10084 : oddCount 10084 15 = 4 ∧ acceleratedOrbit 15 10084 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10084) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10084.1, data_15_10084.2]

/-- Complete interval computation for depth 15, residue 10085. -/
theorem bounds_15_10085 : exactInterval 15 10085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10085 : oddCount 10085 15 = 4 ∧ acceleratedOrbit 15 10085 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10085) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10085.1, data_15_10085.2]

/-- Complete interval computation for depth 15, residue 10086. -/
theorem bounds_15_10086 : exactInterval 15 10086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10086 : oddCount 10086 15 = 4 ∧ acceleratedOrbit 15 10086 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10086) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10086.1, data_15_10086.2]

/-- Complete interval computation for depth 15, residue 10087. -/
theorem bounds_15_10087 : exactInterval 15 10087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10087 : oddCount 10087 15 = 12 ∧ acceleratedOrbit 15 10087 = 163615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10087) = 3 ^ 12 * m + 163615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10087.1, data_15_10087.2]

/-- Complete interval computation for depth 15, residue 10088. -/
theorem bounds_15_10088 : exactInterval 15 10088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10088 : oddCount 10088 15 = 4 ∧ acceleratedOrbit 15 10088 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10088) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10088.1, data_15_10088.2]

/-- Complete interval computation for depth 15, residue 10089. -/
theorem bounds_15_10089 : exactInterval 15 10089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10089 : oddCount 10089 15 = 7 ∧ acceleratedOrbit 15 10089 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10089) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10089.1, data_15_10089.2]

/-- Complete interval computation for depth 15, residue 10090. -/
theorem bounds_15_10090 : exactInterval 15 10090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10090 : oddCount 10090 15 = 4 ∧ acceleratedOrbit 15 10090 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10090) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10090.1, data_15_10090.2]

/-- Complete interval computation for depth 15, residue 10091. -/
theorem bounds_15_10091 : exactInterval 15 10091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10091 : oddCount 10091 15 = 9 ∧ acceleratedOrbit 15 10091 = 6065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10091) = 3 ^ 9 * m + 6065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10091.1, data_15_10091.2]

end Collatz.Research.PassageAtlas.Batch0308
