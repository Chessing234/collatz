import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0198

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 2001. -/
theorem bounds_11_2001 : exactInterval 11 2001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2001 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2001) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2001 : oddCount 2001 11 = 5 ∧ acceleratedOrbit 11 2001 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2001 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2001) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2001.1, data_11_2001.2]

/-- Complete interval computation for depth 11, residue 2002. -/
theorem bounds_11_2002 : exactInterval 11 2002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2002 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2002) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2002 : oddCount 2002 11 = 8 ∧ acceleratedOrbit 11 2002 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2002 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2002) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2002.1, data_11_2002.2]

/-- Complete interval computation for depth 11, residue 2003. -/
theorem bounds_11_2003 : exactInterval 11 2003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2003 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2003) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2003 : oddCount 2003 11 = 8 ∧ acceleratedOrbit 11 2003 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2003 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2003) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2003.1, data_11_2003.2]

/-- Complete interval computation for depth 11, residue 2004. -/
theorem bounds_11_2004 : exactInterval 11 2004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2004 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2004) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2004 : oddCount 2004 11 = 5 ∧ acceleratedOrbit 11 2004 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2004 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2004) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2004.1, data_11_2004.2]

/-- Complete interval computation for depth 11, residue 2005. -/
theorem bounds_11_2005 : exactInterval 11 2005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2005 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2005) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2005 : oddCount 2005 11 = 5 ∧ acceleratedOrbit 11 2005 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2005 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2005) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2005.1, data_11_2005.2]

/-- Complete interval computation for depth 11, residue 2006. -/
theorem bounds_11_2006 : exactInterval 11 2006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2006 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2006) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2006 : oddCount 2006 11 = 7 ∧ acceleratedOrbit 11 2006 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2006 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2006) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2006.1, data_11_2006.2]

/-- Complete interval computation for depth 11, residue 2007. -/
theorem bounds_11_2007 : exactInterval 11 2007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2007 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2007) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2007 : oddCount 2007 11 = 7 ∧ acceleratedOrbit 11 2007 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2007 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2007) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2007.1, data_11_2007.2]

/-- Complete interval computation for depth 11, residue 2008. -/
theorem bounds_11_2008 : exactInterval 11 2008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2008 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2008) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2008 : oddCount 2008 11 = 6 ∧ acceleratedOrbit 11 2008 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2008 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2008) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2008.1, data_11_2008.2]

/-- Complete interval computation for depth 11, residue 2009. -/
theorem bounds_11_2009 : exactInterval 11 2009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2009 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2009) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2009 : oddCount 2009 11 = 4 ∧ acceleratedOrbit 11 2009 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2009 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2009) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2009.1, data_11_2009.2]

/-- Complete interval computation for depth 11, residue 2010. -/
theorem bounds_11_2010 : exactInterval 11 2010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2010 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2010) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2010 : oddCount 2010 11 = 6 ∧ acceleratedOrbit 11 2010 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2010 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2010) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2010.1, data_11_2010.2]

/-- Complete interval computation for depth 11, residue 2011. -/
theorem bounds_11_2011 : exactInterval 11 2011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2011 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2011) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2011 : oddCount 2011 11 = 7 ∧ acceleratedOrbit 11 2011 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2011 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2011) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2011.1, data_11_2011.2]

/-- Complete interval computation for depth 11, residue 2012. -/
theorem bounds_11_2012 : exactInterval 11 2012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2012 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2012) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2012 : oddCount 2012 11 = 6 ∧ acceleratedOrbit 11 2012 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2012 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2012) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2012.1, data_11_2012.2]

/-- Complete interval computation for depth 11, residue 2013. -/
theorem bounds_11_2013 : exactInterval 11 2013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2013 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2013) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2013 : oddCount 2013 11 = 6 ∧ acceleratedOrbit 11 2013 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2013 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2013) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2013.1, data_11_2013.2]

/-- Complete interval computation for depth 11, residue 2014. -/
theorem bounds_11_2014 : exactInterval 11 2014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2014 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2014) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2014 : oddCount 2014 11 = 7 ∧ acceleratedOrbit 11 2014 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2014 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2014) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2014.1, data_11_2014.2]

/-- Complete interval computation for depth 11, residue 2015. -/
theorem bounds_11_2015 : exactInterval 11 2015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2015 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2015) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2015 : oddCount 2015 11 = 7 ∧ acceleratedOrbit 11 2015 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2015 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2015) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2015.1, data_11_2015.2]

/-- Complete interval computation for depth 11, residue 2016. -/
theorem bounds_11_2016 : exactInterval 11 2016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2016 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2016) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2016 : oddCount 2016 11 = 6 ∧ acceleratedOrbit 11 2016 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2016 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2016) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2016.1, data_11_2016.2]

end Collatz.Research.StoppingAtlas.Batch0198
