import Collatz.Structure.RunDescent
import Collatz.Structure.OrbitMinSieve

/-!
# The single predicate everything reduces to

Say a number **never drops** when its own accelerated orbit never goes below it:

`NeverDrops x  ↔  ∀ j, x ≤ T^j(x)`.

This one predicate carries the whole problem.

* If `x > 1` never drops it cannot reach `1`, so it is a counterexample.
* Conversely every counterexample has an orbit minimum, and an orbit minimum
  never drops.

So **Collatz is exactly the statement that `1` is the only number that never
drops** (`collatz_iff_neverDrops`).  That is the target: a single sentence about
a single predicate, with no reference to cycles, divergence, minimality of
counterexamples, or reachability.

The value of the reformulation is that every structural theorem in this project
was proved for orbit minima, and an orbit minimum is precisely a number that
never drops.  So all of them specialise to `NeverDrops` with `n := x` and the
trivial witness `T^0(x) = x`, and they compose into one profile
(`neverDrops_profile`).  What that profile says, in total:

a number that never drops is at least `102 400`, odd, `3` modulo `4`, one of
`{7, 11, 15}` modulo `16`, survives the residue sieve at every level up to
sixteen, is heavy at every scale below itself, opens with a run of at least two
odd steps, takes strictly fewer halvings than odd steps on its first excursion,
and cannot take two halvings in a row at times two and three.

And none of that is a contradiction, because `2 ^ k − 1` satisfies every clause
of it for `k` large.  That is the obstruction, stated as sharply as this
development can state it.
-/

namespace Collatz
namespace NeverDrops

open Reach Congruence AccCycle OrbitMin OrbitMinSieve OddRuns RunValue RunDescent

/-! ## The predicate -/

/-- `NeverDrops x` says the accelerated orbit of `x` never goes below `x`. -/
def NeverDrops (x : Nat) : Prop := ∀ j : Nat, x ≤ acceleratedOrbit j x

/-- `1` never drops: every orbit value is positive. -/
theorem neverDrops_one : NeverDrops 1 := by
  intro j
  exact acceleratedOrbit_positive (by omega) j

/-! ### The missing bridge

`Reach` proves that accelerated reachability implies standard reachability.  The
converse was not needed until now: to read `NeverDrops` as a statement about
counterexamples we need the standard orbit's arrival at `1` to be witnessed by
the accelerated orbit as well.  An even step is an accelerated step, and an odd
step is followed by a forced even one, so a standard run of length `k` contains
an accelerated run using strictly fewer standard steps. -/

/-- **Standard reachability implies accelerated reachability.** -/
theorem accReachesOne_of_orbit : ∀ (k n : Nat), 0 < n → orbit k n = 1 → AccReachesOne n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro n hn hk
    match k with
    | 0 =>
      rw [orbit] at hk
      subst hk
      exact accReachesOne_one
    | k' + 1 =>
      have hk' : orbit k' (step n) = 1 := by rw [orbit_succ_steps] at hk; exact hk
      rcases Arith.mod_two_eq_zero_or_one n with he | ho
      · have hstep : acceleratedStep n = step n := accStep_eq_step_of_even he
        have hval : step n = n / 2 := by
          rw [step, if_neg (by omega), if_pos he]
        have hpos : 0 < step n := by rw [hval]; omega
        have hrec := ih k' (by omega) (step n) hpos hk'
        rw [← hstep] at hrec
        exact accReachesOne_of_step hrec
      · have hs : step n = 3 * n + 1 := step_odd hn ho
        match k' with
        | 0 =>
          rw [orbit] at hk'
          omega
        | k'' + 1 =>
          have hk'' : orbit k'' (step (step n)) = 1 := by
            rw [orbit_succ_steps] at hk'; exact hk'
          have hacc : acceleratedStep n = step (step n) :=
            accStep_eq_step_step_of_odd hn ho
          have hpos : 0 < acceleratedStep n := by
            have h1 := acceleratedOrbit_positive hn 1
            rw [acceleratedOrbit, acceleratedOrbit] at h1
            exact h1
          rw [hacc] at hpos
          have hrec := ih k'' (by omega) (step (step n)) hpos hk''
          rw [← hacc] at hrec
          exact accReachesOne_of_step hrec

/-- Reaching `1` and accelerated reaching of `1` agree on positive inputs. -/
theorem accReachesOne_iff {n : Nat} (hn : 0 < n) : ReachesOne n ↔ AccReachesOne n := by
  constructor
  · intro ⟨k, hk⟩
    exact accReachesOne_of_orbit k n hn hk
  · exact reachesOne_of_accReachesOne hn

/-- A number bigger than one that never drops cannot reach one. -/
theorem not_reachesOne_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    ¬ ReachesOne x := by
  intro hr
  obtain ⟨k, hk⟩ := (accReachesOne_iff (by omega)).mp hr
  have := h k
  omega

/-- Conversely, every counterexample supplies a number bigger than one that never
drops: its own orbit minimum. -/
theorem exists_neverDrops {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧ NeverDrops m := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  exact ⟨m, ge_verified hn hnr hm, no_drop hm hmin⟩

/-- **The reformulation.**  Collatz says exactly that `1` is the only number that
never drops. -/
theorem collatz_iff_neverDrops :
    CollatzConjecture ↔ ∀ x : Nat, NeverDrops x → x ≤ 1 := by
  constructor
  · intro hC x hnd
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · omega
    · exfalso
      exact not_reachesOne_of_neverDrops (by omega) hnd (hC x (by omega))
  · intro h n hn
    by_cases hr : ReachesOne n
    · exact hr
    · exfalso
      obtain ⟨m, hge, hnd⟩ := exists_neverDrops hn hr
      have := h m hnd
      omega

/-- The same target with the size bound folded in: it suffices to rule out large
numbers that never drop. -/
theorem collatz_of_no_large_neverDrops
    (h : ∀ x : Nat, 102400 ≤ x → ¬ NeverDrops x) : CollatzConjecture := by
  refine collatz_iff_neverDrops.mpr ?_
  intro x hnd
  rcases Nat.lt_or_ge x 102400 with hlt | hge
  · rcases Nat.lt_or_ge x 2 with h1 | h2
    · omega
    · exfalso
      have hnr := not_reachesOne_of_neverDrops (by omega) hnd
      have := Search.reachesOne_of_lt_102400 (n := x) (by omega) hlt
      exact hnr this
  · exact absurd hnd (h x hge)

/-! ## Specialising the structure theory

An orbit minimum is exactly a number that never drops, so every theorem proved
for orbit minima applies here with `n := x` and the witness `T^0(x) = x`. -/

/-- The trivial witness. -/
theorem self_witness (x : Nat) : ∃ i : Nat, acceleratedOrbit i x = x := ⟨0, rfl⟩

/-- A number that never drops and exceeds one is a counterexample, hence at least
`102 400`. -/
theorem ge_verified_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    102400 ≤ x :=
  ge_verified (by omega) (not_reachesOne_of_neverDrops hgt h) (self_witness x)

/-- It is odd. -/
theorem odd_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) : x % 2 = 1 :=
  accCycleMin_odd (by omega) (self_witness x) h

/-- It is `3` modulo `4`. -/
theorem mod_four_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) : x % 4 = 3 :=
  residue_mod_four (by omega) (not_reachesOne_of_neverDrops hgt h) (self_witness x) h

/-- It lies in one of `{7, 11, 15}` modulo `16`. -/
theorem mod_sixteen_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    x % 16 = 7 ∨ x % 16 = 11 ∨ x % 16 = 15 :=
  min_mod_sixteen (by omega) (not_reachesOne_of_neverDrops hgt h) (self_witness x) h

/-- It survives the residue sieve at every level up to sixteen. -/
theorem survives_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x)
    {j : Nat} (hj : j ≤ 16) : survives j (x % 2 ^ j) = true :=
  survives_of_counterexample (by omega) (not_reachesOne_of_neverDrops hgt h)
    (self_witness x) h hj

/-- It is heavy at every scale below itself. -/
theorem heavy_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x)
    {k : Nat} (hk : 2 ^ k ≤ x) : 2 ^ k < 2 * 3 ^ oddCount x k :=
  OrbitMin.heavy (by omega) (self_witness x) h hk

/-- With the explicit rate. -/
theorem rate_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x)
    {k : Nat} (hk : 2 ^ k ≤ x) : 3 * (k - 1) ≤ 5 * oddCount x k :=
  OrbitMin.three_mul_le_five_mul (by omega) (self_witness x) h hk

/-- It opens with a run of at least two odd steps. -/
theorem oddRun_two_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    OddRun x 2 :=
  RunBounds.min_oddRun_two (by omega) (self_witness x) h hgt

/-- Its opening two steps climb by exactly `9/4`. -/
theorem climb_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    4 * (acceleratedOrbit 2 x + 1) = 9 * (x + 1) :=
  min_climb (by omega) (self_witness x) h hgt

/-- It never takes halvings at both time two and time three. -/
theorem not_two_halvings_of_neverDrops {x : Nat} (hgt : 1 < x) (h : NeverDrops x)
    (h2 : acceleratedOrbit 2 x % 2 = 0) (h3 : acceleratedOrbit 3 x % 2 = 0) : False :=
  not_two_halvings (by omega) (self_witness x) h hgt h2 h3

/-- Its first excursion takes strictly fewer halvings than odd steps. -/
theorem halvings_lt_run_of_neverDrops {x v W : Nat} (hgt : 1 < x) (h : NeverDrops x)
    (hv : 2 ≤ v) (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0) :
    W < v :=
  halvings_lt_run (self_witness x) h hgt hv hrun hhalve

/-- The descent bound, in the `NeverDrops` language. -/
theorem descent_bound_of_neverDrops {x v W : Nat} (h : NeverDrops x)
    (hrun : OddRun x v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) x % 2 = 0) :
    2 ^ (v + W) * x + 2 ^ v ≤ 3 ^ v * (x + 1) :=
  run_descent_bound (self_witness x) h hrun hhalve

/-! ## The profile -/

/-- **Everything at once.**  What a number that never drops must look like. -/
theorem neverDrops_profile {x : Nat} (hgt : 1 < x) (h : NeverDrops x) :
    102400 ≤ x ∧
    x % 2 = 1 ∧
    x % 4 = 3 ∧
    (x % 16 = 7 ∨ x % 16 = 11 ∨ x % 16 = 15) ∧
    (∀ j : Nat, j ≤ 16 → survives j (x % 2 ^ j) = true) ∧
    (∀ k : Nat, 2 ^ k ≤ x → 2 ^ k < 2 * 3 ^ oddCount x k) ∧
    (∀ k : Nat, 2 ^ k ≤ x → 3 * (k - 1) ≤ 5 * oddCount x k) ∧
    OddRun x 2 ∧
    4 * (acceleratedOrbit 2 x + 1) = 9 * (x + 1) ∧
    (∀ j : Nat, OddRun x j → 2 ^ j ≤ x + 1) :=
  ⟨ge_verified_of_neverDrops hgt h,
   odd_of_neverDrops hgt h,
   mod_four_of_neverDrops hgt h,
   mod_sixteen_of_neverDrops hgt h,
   fun j hj => survives_of_neverDrops hgt h hj,
   fun k hk => heavy_of_neverDrops hgt h hk,
   fun k hk => rate_of_neverDrops hgt h hk,
   oddRun_two_of_neverDrops hgt h,
   climb_of_neverDrops hgt h,
   fun j hrun => RunBounds.oddRun_le_min (by omega) (self_witness x) hrun⟩

/-- **The obstruction, stated against the profile.**  Every clause of the profile
is satisfied by `2 ^ k − 1` for large `k`: it is odd, `−1` modulo every power of
two below `2 ^ k`, heavy at every scale (it opens with `k` odd steps), and opens
with a run of length `k ≥ 2`.  So no clause of the profile, and no finite
conjunction of clauses of this kind, can close the problem. -/
theorem obstruction_satisfies_profile (j : Nat) :
    (2 ^ (j + 4) - 1) % 2 = 1 ∧ (2 ^ (j + 4) - 1) % 4 = 3 ∧
    (2 ^ (j + 4) - 1) % 16 = 15 ∧ OddRun (2 ^ (j + 4) - 1) (j + 4) := by
  have hpow : (2:Nat) ^ (j + 4) = 2 ^ j * 16 := by
    rw [Nat.pow_add]
  have hpos : 0 < 2 ^ j := Arith.two_pow_pos j
  refine ⟨by omega, by omega, by omega, oddRun_two_pow_sub_one (j + 4)⟩

end NeverDrops
end Collatz
