import Collatz.Structure.RunValue

/-!
# What must follow a run

A run of `j` odd steps multiplies `x + 1` by exactly `(3/2) ^ j`
(`RunValue.oddRun_value`).  The halvings that follow divide by `2` each time.
At the orbit minimum of a counterexample the orbit is never allowed below `m`,
and those two facts together pin down how many halvings may follow a run.

Write the run as length `v` and let `W` halvings follow.  Then

* `2 ^ W · T^{v+W}(m) = T^v(m)` — the halvings are exact,
* `T^{v+W}(m) ≥ m` — the minimum is never undercut,
* `2 ^ v · (T^v(m) + 1) = 3 ^ v · (m + 1)` — the run is exact.

Eliminating `T^v(m)` gives the master inequality

`2 ^ (v + W) · m + 2 ^ v ≤ 3 ^ v · (m + 1)`.

This is heaviness without slack.  `OrbitMin.three_mul_le_five_mul` gives
`a ≥ 3(k−1)/5` by an averaging argument; the inequality above is the same
phenomenon stated exactly, step by step, and it is sharp enough to forbid
configurations the averaging bound permits.

The immediate consequence: since the minimum begins a run of length at least two
and is at least `102 400`, **two halvings can never follow it**.  Taking `v = 2`
and `W = 2` gives `16 m + 4 ≤ 9 m + 9`, i.e. `7 m ≤ 5`, which is absurd.  So the
step at time `3` is forced to be odd whenever the step at time `2` is even — a
forced step with no tightness hypothesis at all, unlike `ForcedSteps`.
-/

namespace Collatz
namespace RunDescent

open Reach Congruence AccCycle OrbitMin OddRuns RunValue

/-! ## Halvings are exact -/

/-- **A chain of halvings is an exact division.**  If the first `W` steps from
`y` are all even, then `y = 2 ^ W · T^W(y)`. -/
theorem halving_chain : ∀ (W y : Nat), (∀ i : Nat, i < W → acceleratedOrbit i y % 2 = 0) →
    2 ^ W * acceleratedOrbit W y = y := by
  intro W
  induction W with
  | zero =>
    intro y _
    rw [acceleratedOrbit]
    simp
  | succ W ih =>
    intro y h
    have heven : y % 2 = 0 := by
      have := h 0 (by omega)
      rw [acceleratedOrbit] at this
      exact this
    have hstep : acceleratedStep y = y / 2 := by
      rw [acceleratedStep, if_pos heven]
    have htail : ∀ i : Nat, i < W → acceleratedOrbit i (acceleratedStep y) % 2 = 0 := by
      intro i hi
      have := h (i + 1) (by omega)
      rw [show acceleratedOrbit (i + 1) y = acceleratedOrbit i (acceleratedStep y) from rfl] at this
      exact this
    have hrec := ih (acceleratedStep y) htail
    rw [hstep] at hrec
    have hshift : acceleratedOrbit (W + 1) y = acceleratedOrbit W (acceleratedStep y) := rfl
    have hA : (2:Nat) ^ (W + 1) * acceleratedOrbit (W + 1) y
        = 2 * (2 ^ W * acceleratedOrbit W (acceleratedStep y)) := by
      rw [hshift, Arith.two_pow_succ, Nat.mul_assoc]
    rw [hA, hstep, hrec]
    omega

/-! ## The master inequality -/

/-- **How many halvings may follow a run.**  At the orbit minimum, a run of
length `v` followed by `W` halvings forces
`2 ^ (v + W) · m + 2 ^ v ≤ 3 ^ v · (m + 1)`. -/
theorem run_descent_bound {n m v W : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hrun : OddRun m v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) m % 2 = 0) :
    2 ^ (v + W) * m + 2 ^ v ≤ 3 ^ v * (m + 1) := by
  -- the halvings, applied to the value at the end of the run
  have hshift : ∀ i : Nat, acceleratedOrbit i (acceleratedOrbit v m) = acceleratedOrbit (v + i) m := by
    intro i
    rw [acceleratedOrbit_add, Nat.add_comm]
  have htail : ∀ i : Nat, i < W → acceleratedOrbit i (acceleratedOrbit v m) % 2 = 0 := by
    intro i hi
    rw [hshift i]
    exact hhalve i hi
  have hchain := halving_chain W (acceleratedOrbit v m) htail
  rw [hshift W] at hchain
  -- the minimum is never undercut
  have hno : m ≤ acceleratedOrbit (v + W) m := no_drop hm hmin (v + W)
  have hge : 2 ^ W * m ≤ acceleratedOrbit v m := by
    have hmono : 2 ^ W * m ≤ 2 ^ W * acceleratedOrbit (v + W) m :=
      Nat.mul_le_mul_left _ hno
    omega
  -- the run is exact
  have hval := oddRun_value v m hrun
  have hmul : 2 ^ v * (2 ^ W * m) ≤ 2 ^ v * acceleratedOrbit v m :=
    Nat.mul_le_mul_left _ hge
  calc 2 ^ (v + W) * m + 2 ^ v
      = 2 ^ v * (2 ^ W * m) + 2 ^ v := by rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 2 ^ v * acceleratedOrbit v m + 2 ^ v := Nat.add_le_add_right hmul _
    _ = 2 ^ v * (acceleratedOrbit v m + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = 3 ^ v * (m + 1) := hval

/-! ## Two halvings never follow the minimum -/

/-- The orbit minimum begins a run of length two, so the bound applies with
`v = 2`. -/
theorem two_run_descent_bound {n m W : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (2 + i) m % 2 = 0) :
    2 ^ (2 + W) * m + 4 ≤ 9 * (m + 1) := by
  have hrun := RunBounds.min_oddRun_two hn hm hmin hgt
  have hb := run_descent_bound hm hmin hrun hhalve
  have h9 : (3:Nat) ^ 2 = 9 := by decide
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  rw [h9, h4] at hb
  exact hb

/-- **Two halvings cannot follow the minimum's opening run.**  Taking `W = 2`
gives `16 m + 4 ≤ 9 m + 9`, so `7 m ≤ 5` — impossible for `m > 1`. -/
theorem not_two_halvings {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (h2 : acceleratedOrbit 2 m % 2 = 0) (h3 : acceleratedOrbit 3 m % 2 = 0) :
    False := by
  have hhalve : ∀ i : Nat, i < 2 → acceleratedOrbit (2 + i) m % 2 = 0 := by
    intro i hi
    cases i with
    | zero => exact h2
    | succ i' =>
      have : i' = 0 := by omega
      subst this
      exact h3
  have hb := two_run_descent_bound hn hm hmin hgt hhalve
  have h16 : (2:Nat) ^ (2 + 2) = 16 := by decide
  rw [h16] at hb
  omega

/-- **A forced odd step at time three.**  If the minimum's run has length exactly
two — that is, if the step at time two is a halving — then the step at time three
is forced to be odd. -/
theorem forced_odd_at_three {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (h2 : acceleratedOrbit 2 m % 2 = 0) :
    acceleratedOrbit 3 m % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit 3 m) with he | ho
  · exact absurd (not_two_halvings hn hm hmin hgt h2 he) (fun h => h)
  · exact ho

/-! ## A new residue class is excluded -/

/-- On the class `3 mod 8` the opening run has length exactly two, so the step at
time two is a halving. -/
theorem even_at_two_of_mod_eight {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (h8 : m % 8 = 3) :
    acceleratedOrbit 2 m % 2 = 0 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit 2 m) with he | ho
  · exact he
  · exfalso
    have hrun : OddRun m 3 := by
      intro i hi
      have hrun2 := RunBounds.min_oddRun_two hn hm hmin hgt
      cases i with
      | zero => exact hrun2 0 (by omega)
      | succ i' =>
        cases i' with
        | zero => exact hrun2 1 (by omega)
        | succ i'' =>
          have : i'' = 0 := by omega
          subst this
          exact ho
    have := RunBounds.min_mod_eight_of_run_three hrun
    omega

/-- **The orbit minimum is never `3` modulo `16`.**

On `3 mod 8` the run has length two, so `T²(m)` is even; the descent bound then
forces `T³(m)` to be odd.  But `4 (T²(m) + 1) = 9 (m + 1)` with `m ≡ 3 (mod 16)`
makes `T²(m)` divisible by four, so `T³(m)` is even.  The two are incompatible.

Combined with `m ≡ 3 (mod 4)`, the minimum lies in `{7, 11, 15}` modulo `16`. -/
theorem min_ne_three_mod_sixteen {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (h16 : m % 16 = 3) : False := by
  have h8 : m % 8 = 3 := by omega
  have h2 := even_at_two_of_mod_eight hn hm hmin hgt h8
  have h3 := forced_odd_at_three hn hm hmin hgt h2
  have hex := two_step_exact (m := m) (by omega)
  -- `T³(m)` is `T²(m)` halved, and `T²(m)` is divisible by four
  have hstep : acceleratedOrbit 3 m = acceleratedOrbit 2 m / 2 := by
    rw [show acceleratedOrbit 3 m = acceleratedStep (acceleratedOrbit 2 m) from
      acceleratedOrbit_succ_step 2 m, acceleratedStep, if_pos h2]
  rw [hstep] at h3
  omega

/-- **The minimum modulo sixteen.**  Only three of the sixteen classes remain.

These are exactly the classes the residue sieve leaves at level four —
`(List.range 16).filter (survives 4)` evaluates to `[7, 11, 15]`.  The sieve is
therefore not a computational accident: at this level it is precisely the
run-and-halving bookkeeping above, carried out by search instead of by algebra.
That identification is the useful part, because it says what the sieve is
*doing*, and hence why enlarging it cannot terminate: each level asks the same
question about one more halving, and the class `−1 mod 2^k` always answers it. -/
theorem min_mod_sixteen {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    m % 16 = 7 ∨ m % 16 = 11 ∨ m % 16 = 15 := by
  have hge := ge_verified hn hnr hm
  have hfour := OrbitMinSieve.residue_mod_four hn hnr hm hmin
  rcases (show m % 16 = 3 ∨ m % 16 = 7 ∨ m % 16 = 11 ∨ m % 16 = 15 by omega) with h | h | h | h
  · exact absurd (min_ne_three_mod_sixteen hn hm hmin (by omega) h) (fun hf => hf)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## Longer runs -/

/-- With a run of length three the same computation gives `32 m + 8 ≤ 27 m + 27`,
so `5 m ≤ 19`: two halvings are impossible there too. -/
theorem not_two_halvings_of_run_three {n m : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 4 < m)
    (hrun : OddRun m 3)
    (h3 : acceleratedOrbit 3 m % 2 = 0) (h4 : acceleratedOrbit 4 m % 2 = 0) :
    False := by
  have hhalve : ∀ i : Nat, i < 2 → acceleratedOrbit (3 + i) m % 2 = 0 := by
    intro i hi
    cases i with
    | zero => exact h3
    | succ i' =>
      have : i' = 0 := by omega
      subst this
      exact h4
  have hb := run_descent_bound hm hmin hrun hhalve
  have h32 : (2:Nat) ^ (3 + 2) = 32 := by decide
  have h27 : (3:Nat) ^ 3 = 27 := by decide
  have h8 : (2:Nat) ^ 3 = 8 := by decide
  rw [h32, h27, h8] at hb
  omega

/-- **The general trade-off.**  Either the halvings are few enough that
`2 ^ (v + W) ≤ 3 ^ v`, or the minimum is small enough to be checked directly.
Since the minimum of a counterexample is at least `102 400`, only the first
alternative survives, so `W ≤ v · log₂(3/2)`. -/
theorem pow_dichotomy {n m v W : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hrun : OddRun m v)
    (hhalve : ∀ i : Nat, i < W → acceleratedOrbit (v + i) m % 2 = 0) :
    2 ^ (v + W) ≤ 3 ^ v ∨ m ≤ 3 ^ v := by
  have hb := run_descent_bound hm hmin hrun hhalve
  by_cases hle : 2 ^ (v + W) ≤ 3 ^ v
  · exact Or.inl hle
  · refine Or.inr ?_
    have hgt : 3 ^ v + 1 ≤ 2 ^ (v + W) := by omega
    have hmono : (3 ^ v + 1) * m ≤ 2 ^ (v + W) * m := Nat.mul_le_mul_right _ hgt
    have key : 3 ^ v * m + m + 2 ^ v ≤ 3 ^ v * m + 3 ^ v := by
      calc 3 ^ v * m + m + 2 ^ v
          = (3 ^ v + 1) * m + 2 ^ v := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2 ^ (v + W) * m + 2 ^ v := Nat.add_le_add_right hmono _
        _ ≤ 3 ^ v * (m + 1) := hb
        _ = 3 ^ v * m + 3 ^ v := by rw [Nat.mul_add, Nat.mul_one]
    have hcancel : m + 2 ^ v ≤ 3 ^ v := by
      refine Nat.le_of_add_le_add_left (a := 3 ^ v * m) ?_
      calc 3 ^ v * m + (m + 2 ^ v) = 3 ^ v * m + m + 2 ^ v := by rw [Nat.add_assoc]
        _ ≤ 3 ^ v * m + 3 ^ v := key
    exact Nat.le_trans (Nat.le_add_right m (2 ^ v)) hcancel

end RunDescent
end Collatz
