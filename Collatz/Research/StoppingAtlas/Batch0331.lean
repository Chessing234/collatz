import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0331

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1996. -/
theorem bounds_12_1996 : exactInterval 12 1996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1996 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1996) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1996 : oddCount 1996 12 = 5 ∧ acceleratedOrbit 12 1996 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1996 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1996) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1996.1, data_12_1996.2]

/-- Complete interval computation for depth 12, residue 1997. -/
theorem bounds_12_1997 : exactInterval 12 1997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1997 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1997) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1997 : oddCount 1997 12 = 5 ∧ acceleratedOrbit 12 1997 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1997 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1997) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1997.1, data_12_1997.2]

/-- Complete interval computation for depth 12, residue 1998. -/
theorem bounds_12_1998 : exactInterval 12 1998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1998 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1998) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1998 : oddCount 1998 12 = 6 ∧ acceleratedOrbit 12 1998 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1998 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1998) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1998.1, data_12_1998.2]

/-- Complete interval computation for depth 12, residue 1999. -/
theorem bounds_12_1999 : exactInterval 12 1999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1999 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1999) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1999 : oddCount 1999 12 = 6 ∧ acceleratedOrbit 12 1999 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1999 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1999) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1999.1, data_12_1999.2]

/-- Complete interval computation for depth 12, residue 2000. -/
theorem bounds_12_2000 : exactInterval 12 2000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2000 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2000) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2000 : oddCount 2000 12 = 5 ∧ acceleratedOrbit 12 2000 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2000 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2000) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2000.1, data_12_2000.2]

/-- Complete interval computation for depth 12, residue 2001. -/
theorem bounds_12_2001 : exactInterval 12 2001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2001 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2001) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2001 : oddCount 2001 12 = 5 ∧ acceleratedOrbit 12 2001 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2001 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2001) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2001.1, data_12_2001.2]

/-- Complete interval computation for depth 12, residue 2002. -/
theorem bounds_12_2002 : exactInterval 12 2002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2002 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2002) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2002 : oddCount 2002 12 = 9 ∧ acceleratedOrbit 12 2002 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2002 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2002) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2002.1, data_12_2002.2]

/-- Complete interval computation for depth 12, residue 2003. -/
theorem bounds_12_2003 : exactInterval 12 2003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2003 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2003) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2003 : oddCount 2003 12 = 9 ∧ acceleratedOrbit 12 2003 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2003 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2003) = 3 ^ 9 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2003.1, data_12_2003.2]

/-- Complete interval computation for depth 12, residue 2004. -/
theorem bounds_12_2004 : exactInterval 12 2004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2004 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2004) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2004 : oddCount 2004 12 = 5 ∧ acceleratedOrbit 12 2004 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2004 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2004) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2004.1, data_12_2004.2]

/-- Complete interval computation for depth 12, residue 2005. -/
theorem bounds_12_2005 : exactInterval 12 2005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2005 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2005) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2005 : oddCount 2005 12 = 5 ∧ acceleratedOrbit 12 2005 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2005 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2005) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2005.1, data_12_2005.2]

/-- Complete interval computation for depth 12, residue 2006. -/
theorem bounds_12_2006 : exactInterval 12 2006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2006 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2006) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2006 : oddCount 2006 12 = 7 ∧ acceleratedOrbit 12 2006 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2006 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2006) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2006.1, data_12_2006.2]

/-- Complete interval computation for depth 12, residue 2007. -/
theorem bounds_12_2007 : exactInterval 12 2007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2007 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2007) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2007 : oddCount 2007 12 = 7 ∧ acceleratedOrbit 12 2007 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2007 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2007) = 3 ^ 7 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2007.1, data_12_2007.2]

/-- Complete interval computation for depth 12, residue 2008. -/
theorem bounds_12_2008 : exactInterval 12 2008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2008 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2008) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2008 : oddCount 2008 12 = 7 ∧ acceleratedOrbit 12 2008 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2008 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2008) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2008.1, data_12_2008.2]

/-- Complete interval computation for depth 12, residue 2009. -/
theorem bounds_12_2009 : exactInterval 12 2009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2009 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2009) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2009 : oddCount 2009 12 = 4 ∧ acceleratedOrbit 12 2009 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2009 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2009) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2009.1, data_12_2009.2]

/-- Complete interval computation for depth 12, residue 2010. -/
theorem bounds_12_2010 : exactInterval 12 2010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2010 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2010) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2010 : oddCount 2010 12 = 7 ∧ acceleratedOrbit 12 2010 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2010 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2010) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2010.1, data_12_2010.2]

/-- Complete interval computation for depth 12, residue 2011. -/
theorem bounds_12_2011 : exactInterval 12 2011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2011 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2011) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2011 : oddCount 2011 12 = 7 ∧ acceleratedOrbit 12 2011 = 1075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2011 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2011) = 3 ^ 7 * m + 1075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2011.1, data_12_2011.2]

end Collatz.Research.StoppingAtlas.Batch0331
