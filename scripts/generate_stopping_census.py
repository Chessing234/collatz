#!/usr/bin/env python3
"""Generate memory-bounded kernel computations of complete event-period counts."""
from descent_intervals import trace


def census_source():
    s='''import Collatz.Research.StoppingAtlas.Discrepancy

namespace Collatz.Research.StoppingAtlas
open PeriodicCounting
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Split a counting window into a prefix and a translated suffix. -/
theorem count_shift_add (P : Nat → Bool) (N M : Nat) :
    countBelow P (N + M) = countBelow P N + countBelow (fun n => P (N + n)) M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_succ, count_succ, ih, count_succ]
    omega

'''
    for k in range(10,14):
        total=0
        s+=f'theorem prefix_{k}_0 : countBelow (firstEventB {k}) 0 = 0 := rfl\n\n'
        for j in range((1<<k)//128):
            base=128*j
            count=0
            for n in range(base+2,base+130):
                _,a=trace(n,k)
                count+=3**a[k]<1<<k and all(1<<i<=3**a[i] for i in range(k))
            s+=f'''/-- Kernel computation on one translated 128-input block. -/
theorem chunk_{k}_{j} : countBelow (fun n => firstEventB {k} ({base} + n)) 128 = {count} := by decide

/-- Assemble independently checked blocks using the general counting identity. -/
theorem prefix_{k}_{j+1} : countBelow (firstEventB {k}) {base+128} = {total+count} := by
  have h := count_shift_add (firstEventB {k}) {base} 128
  rw [prefix_{k}_{j}, chunk_{k}_{j}] at h
  exact h

'''
            total+=count
        s+=f'/-- Complete period numerator at depth {k}. -/\ntheorem period_count_{k} : countBelow (firstEventB {k}) (2 ^ {k}) = {total} := prefix_{k}_{(1<<k)//128}\n\n'
    s+='''/-- Numerical error bar at depth thirteen, valid at every cutoff. -/
theorem depth_thirteen_error (N : Nat) :
    8192 * countBelow (firstEventB 13) N ≤ N * 85 + 689095 ∧
    N * 85 ≤ 8192 * countBelow (firstEventB 13) N + 689095 := by
  have h := firstEvent_composition_error 13 N
  dsimp only at h
  rw [period_count_13] at h
  simpa only [show (2 : Nat) ^ 13 = 8192 by decide,
    show (8192 - 85 : Nat) = 8107 by decide, show (85 * 8107 : Nat) = 689095 by decide] using h

end Collatz.Research.StoppingAtlas
'''
    return s
