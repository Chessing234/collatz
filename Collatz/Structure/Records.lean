import Collatz.Structure.OrbitMinSieve
import Collatz.Core.Minimum
import Collatz.Structure.AccDivergence
import Collatz.Structure.CycleModThree

/-!
# Record highs

The cycle theory got traction from the *greatest* point of a cycle: its
predecessor has to be odd, because an even predecessor would be twice the
maximum and so exceed it.  A divergent orbit has no greatest point — but it has
infinitely many **record highs**, and the same argument applies verbatim to each
one.

`IsRecord n i` says `T^i(n)` exceeds every earlier value of the orbit.  Then:

* the step *into* a record is an odd step (an even step would have arrived from
  something larger);
* hence every record is the image of the odd branch, so **every record high is
  `2` modulo `3`** and in particular is never divisible by three;
* and a divergent orbit has records beyond every bound.

So a divergent orbit visits the class `2 mod 3` infinitely often, and its record
values avoid the multiples of three entirely.  This is the divergence-half
counterpart of `CycleMaxClass.cycleMax_mod_six`, and it needs no boundedness.
-/

namespace Collatz
namespace Records

open Reach Congruence AccCycle

/-! ## Records -/

/-- `IsRecord n i` says the `i`-th value of the orbit of `n` exceeds every
earlier one. -/
def IsRecord (n i : Nat) : Prop :=
  ∀ j : Nat, j < i → acceleratedOrbit j n < acceleratedOrbit i n

/-- **The step into a record is an odd step.**  An even step arrives from twice
its result, which would be a larger earlier value. -/
theorem step_into_record_odd {n i : Nat} (h : IsRecord n (i + 1)) :
    acceleratedOrbit i n % 2 = 1 := by
  have hlt : acceleratedOrbit i n < acceleratedOrbit (i + 1) n := h i (by omega)
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i n) with he | ho
  · exfalso
    have hstep : acceleratedOrbit (i + 1) n = acceleratedOrbit i n / 2 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos he]
    rw [hstep] at hlt
    omega
  · exact ho

/-- **Every record high is `2` modulo `3`.**  It is the image of an odd step, and
the odd branch always lands in that class. -/
theorem record_mod_three {n i : Nat} (h : IsRecord n (i + 1)) :
    acceleratedOrbit (i + 1) n % 3 = 2 := by
  have hodd := step_into_record_odd h
  have hstep : acceleratedOrbit (i + 1) n = acceleratedStep (acceleratedOrbit i n) :=
    acceleratedOrbit_succ_step i n
  rw [hstep]
  exact CycleModThree.accStep_mod_three_of_odd hodd

/-- Record highs are never divisible by three. -/
theorem not_three_dvd_record {n i : Nat} (h : IsRecord n (i + 1)) :
    ¬ 3 ∣ acceleratedOrbit (i + 1) n := by
  have := record_mod_three h
  omega

/-! ## Divergent orbits have unbounded records -/

/-- **A divergent orbit has a record beyond every bound.**  Take the first index
at which the orbit exceeds `B`; everything before it is at most `B`. -/
theorem exists_record_above {n : Nat} (hdiv : AccDivergence.AccDivergent n) (B : Nat) :
    ∃ i : Nat, IsRecord n i ∧ B < acceleratedOrbit i n := by
  obtain ⟨i, hi, hmin⟩ :=
    Minimum.exists_min (P := fun j => B < acceleratedOrbit j n) (hdiv B)
  refine ⟨i, fun j hj => ?_, hi⟩
  have hle : ¬ (B < acceleratedOrbit j n) := hmin j hj
  omega

/-- Hence a divergent orbit meets the class `2 mod 3` at arbitrarily large
values. -/
theorem divergent_hits_two_mod_three {n : Nat} (hdiv : AccDivergence.AccDivergent n)
    (B : Nat) : ∃ i : Nat, B < acceleratedOrbit i n ∧
      (i = 0 ∨ acceleratedOrbit i n % 3 = 2) := by
  obtain ⟨i, hrec, hgt⟩ := exists_record_above hdiv B
  cases i with
  | zero => exact ⟨0, hgt, Or.inl rfl⟩
  | succ j => exact ⟨j + 1, hgt, Or.inr (record_mod_three hrec)⟩

/-- A divergent orbit therefore takes infinitely many odd steps: past every
bound there is a record, and the step into it is odd. -/
theorem divergent_odd_steps_unbounded {n : Nat} (hdiv : AccDivergence.AccDivergent n)
    (B : Nat) : ∃ i : Nat, B < acceleratedOrbit (i + 1) n ∧
      acceleratedOrbit i n % 2 = 1 := by
  obtain ⟨i, hrec, hgt⟩ := exists_record_above hdiv (Nat.max B (acceleratedOrbit 0 n))
  cases i with
  | zero =>
    exfalso
    have hle : acceleratedOrbit 0 n ≤ Nat.max B (acceleratedOrbit 0 n) :=
      Nat.le_max_right _ _
    omega
  | succ j =>
    refine ⟨j, ?_, step_into_record_odd hrec⟩
    have hle : B ≤ Nat.max B (acceleratedOrbit 0 n) := Nat.le_max_left _ _
    omega

/-! ## The maximum of a bounded orbit is a record -/

/-- On a cycle the greatest point is a record, so `CycleMaxClass.cycleMax_mod_six`
is the bounded case of `record_mod_three`. -/
theorem record_of_strict_max {n i : Nat}
    (hmax : ∀ j : Nat, j < i → acceleratedOrbit j n < acceleratedOrbit i n) :
    IsRecord n i := hmax

/-- The two halves side by side: a bounded counterexample has a greatest point
`2` modulo `3`, and a divergent one has records `2` modulo `3` beyond every
bound. -/
theorem records_classify {n : Nat} (hdiv : AccDivergence.AccDivergent n) (B : Nat) :
    ∃ i : Nat, B < acceleratedOrbit (i + 1) n ∧
      acceleratedOrbit (i + 1) n % 3 = 2 := by
  obtain ⟨i, hrec, hgt⟩ := exists_record_above hdiv (Nat.max B (acceleratedOrbit 0 n))
  cases i with
  | zero =>
    exfalso
    have hle : acceleratedOrbit 0 n ≤ Nat.max B (acceleratedOrbit 0 n) :=
      Nat.le_max_right _ _
    omega
  | succ j =>
    refine ⟨j, ?_, record_mod_three hrec⟩
    have hle : B ≤ Nat.max B (acceleratedOrbit 0 n) := Nat.le_max_left _ _
    omega

end Records
end Collatz
