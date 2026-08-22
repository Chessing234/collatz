import Collatz.Strategy.RepetitionDescent

/-!
# The accumulator is a partition function with no temperature

Round X was asked whether the orbit blocks of a Collatz trajectory carry a
statistical-mechanical partition function whose *dominant configurations* are the
non-descending trajectories, and whether that partition function has a **phase
transition**.

This file answers the question by an exact identity, and the answer is no — for a
reason sharper than "it reproduces the `0.05004·L` surplus".

## The set-up

Round IX's postscript (`Collatz/Strategy/Coupling.lean`) proved that the one open bit
of the archimedean/2-adic bridge is the single ratio

`r j = C j / (3 ^ (A j) · n)`,

the accumulator measured against the orbit point.  Expanding `C` gives a Laplace sum:

`C_L(w) = Σ_{i : w i = 1} 3 ^ (a − A_{i+1}) · 2 ^ i`,

so, writing the critical-density discrepancy as `D̃(i) = A_{i+1} − i·log₃2`,

`C_L(w) = 3 ^ a · Σ_{i : w i = 1} 3 ^ (−D̃(i))`.

That **is** a partition function: configurations are the odd positions of the word,
the energy of the configuration at position `i` is the discrepancy `D̃(i)`, and the
Boltzmann weight is `3 ^ (−D̃(i))`.  The physical inverse temperature is therefore

> `β = 1`, **pinned**, because the `3` in the Boltzmann weight is the same `3` as in
> `3x + 1`.

There is no temperature knob.  A partition function with no free `β` has no phase
diagram: its phase diagram is a point.

## The theorem: the sum is its own largest term

`wTermMax` is the largest Boltzmann weight, `wC` the partition function.  The two
theorems below are

`wTermMax_le_wC`      :  `wTermMax w ≤ wC w`
`wC_le_ones_mul_max`  :  `wC w ≤ ones w * wTermMax w`

so `wC w` and `wTermMax w` agree to within a factor of `a = ones w`.  In physical
language: **the free energy equals the ground-state energy up to `log₃ a`**.  The
entropy contribution to the pressure is `O(log a)` — sub-extensive, hence zero
pressure density.  The system is frozen at every word, not merely at bad words, so
there is no phase to transition to and no "bad phase" to isolate.

## The ground state is the discrepancy minimum

`term_le_wTermMax` exhibits every Boltzmann weight explicitly: for `w = u ++ 1 :: v`
the odd position at time `u.length` contributes `2 ^ u.length * 3 ^ ones v`, and

`term_disc_identity` : `3 ^ (ones u + 1) * (2 ^ u.length * 3 ^ ones v)
                        = 3 ^ ones (u ++ 1 :: v) * 2 ^ u.length`,

which is the log-free form of `log₃(weight) = a − A_{i+1} + i·log₃2 = a − D̃(i)`.
Maximising the weight is *exactly* minimising the discrepancy.  So the ground-state
energy is `min_i D̃(i)` and the free energy is `a − min_i D̃(i)` up to `log₃ a`.

## What this costs the programme

`cycle_ground_state` feeds the sandwich through the cycle equation `G · n = C`:

`wTermMax w ≤ G * n ≤ ones w * wTermMax w`.

So on a cycle the minimum element `n` is determined, to within a factor of `a`, by
the **minimum of the discrepancy path**.  That is not a new bound — it is the
statement that the cycle minimum is a *Class 1* quantity in the sense of
`CLOSURE.md`, proved rather than observed.  Every partition-function attack on the
cycle half therefore lands in Class 1 before it starts, and Class 1 is `d`-free
(`C(w, d) = d · C(w, 1)` scales both sides of the sandwich by `d`), so the soundness
filter refutes it with the genuine cycles of `3x−1`, `3x+5`, `3x+7`, `3x+11`,
`3x+13`.

**Admission-rule verdict, stated honestly**: `wTermMax` *fails* the New Object Rule.
It is determined by the word, and its logarithm is `a − min_i D̃(i)`, a function of
the discrepancy path.  It is admitted here not as a discriminator — it cannot be one
— but as the exact identity that shows the partition-function programme is Class 1
rather than a new mechanism.  A device that kills a programme need not survive the
rule the programme was supposed to survive.
-/

namespace Collatz
namespace GroundState

open RepetitionDescent

/-! ## The largest Boltzmann weight -/

/-- The largest summand of `wC`.  Same head recursion as `wC`, with `max` in place
of `+`: the ground-state weight of the word. -/
def wTermMax : List Nat → Nat
  | [] => 0
  | b :: t => Nat.max (if b = 1 then 3 ^ ones t else 0) (2 * wTermMax t)

@[simp] theorem wTermMax_nil : wTermMax [] = 0 := rfl

theorem wTermMax_cons (b : Nat) (t : List Nat) :
    wTermMax (b :: t) = Nat.max (if b = 1 then 3 ^ ones t else 0) (2 * wTermMax t) := rfl

/-! ## The sandwich: free energy = ground-state energy, up to `log₃ a` -/

/-- **Lower half.**  The partition function is at least its largest term. -/
theorem wTermMax_le_wC : ∀ w : List Nat, wTermMax w ≤ wC w := by
  intro w
  induction w with
  | nil => simp
  | cons b t ih =>
      rw [wTermMax_cons, wC_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- **Upper half.**  The partition function is at most `a` times its largest term:
the entropy contributes a factor `a`, not an exponential. -/
theorem wC_le_ones_mul_max : ∀ w : List Nat, wC w ≤ ones w * wTermMax w := by
  intro w
  induction w with
  | nil => simp
  | cons b t ih =>
      by_cases hb : b = 1
      · subst hb
        rw [wTermMax_cons, wC_cons, ones_cons]
        simp only [reduceIte]
        have h1 : 3 ^ ones t ≤ Nat.max (3 ^ ones t) (2 * wTermMax t) :=
          Nat.le_max_left _ _
        have h2 : 2 * wTermMax t ≤ Nat.max (3 ^ ones t) (2 * wTermMax t) :=
          Nat.le_max_right _ _
        have h3 : ones t * (2 * wTermMax t)
            ≤ ones t * Nat.max (3 ^ ones t) (2 * wTermMax t) := Nat.mul_le_mul_left _ h2
        have h4 : 2 * wC t ≤ 2 * (ones t * wTermMax t) := Nat.mul_le_mul_left _ ih
        have h5 : (1 + ones t) * Nat.max (3 ^ ones t) (2 * wTermMax t)
            = Nat.max (3 ^ ones t) (2 * wTermMax t)
              + ones t * Nat.max (3 ^ ones t) (2 * wTermMax t) := by
          rw [Nat.add_mul, Nat.one_mul]
        have h6 : ones t * (2 * wTermMax t) = 2 * (ones t * wTermMax t) := by
          rw [Nat.mul_left_comm]
        omega
      · rw [wTermMax_cons, wC_cons, ones_cons]
        simp only [if_neg hb]
        have h7 : Nat.max 0 (2 * wTermMax t) = 2 * wTermMax t :=
          Nat.max_eq_right (Nat.zero_le _)
        rw [h7, Nat.zero_add, Nat.zero_add]
        have h4 : 2 * wC t ≤ 2 * (ones t * wTermMax t) := Nat.mul_le_mul_left _ ih
        have h6 : ones t * (2 * wTermMax t) = 2 * (ones t * wTermMax t) := by
          rw [Nat.mul_left_comm]
        omega

/-! ## Every Boltzmann weight, explicitly -/

/-- **The weight at one odd position.**  In `w = u ++ 1 :: v` the odd letter at time
`u.length` contributes the summand `2 ^ u.length * 3 ^ ones v`, and it is at most the
ground-state weight. -/
theorem term_le_wTermMax : ∀ u v : List Nat,
    2 ^ u.length * 3 ^ ones v ≤ wTermMax (u ++ 1 :: v) := by
  intro u
  induction u with
  | nil =>
      intro v
      rw [List.nil_append, wTermMax_cons, if_pos rfl]
      have h : 3 ^ ones v ≤ Nat.max (3 ^ ones v) (2 * wTermMax v) := Nat.le_max_left _ _
      simpa using h
  | cons b u ih =>
      intro v
      rw [List.cons_append, wTermMax_cons]
      have h := ih v
      have h2 : 2 * wTermMax (u ++ 1 :: v) ≤
          Nat.max (if b = 1 then 3 ^ ones (u ++ 1 :: v) else 0)
            (2 * wTermMax (u ++ 1 :: v)) := Nat.le_max_right _ _
      have h3 : 2 * (2 ^ u.length * 3 ^ ones v) ≤ 2 * wTermMax (u ++ 1 :: v) :=
        Nat.mul_le_mul_left _ h
      have h4 : 2 ^ (b :: u).length * 3 ^ ones v = 2 * (2 ^ u.length * 3 ^ ones v) := by
        rw [List.length_cons, Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ u.length) 2, Nat.mul_assoc]
      omega

/-- **The weight is the discrepancy, log-free.**  `3 ^ (A_{i+1}) · weight_i
= 3 ^ a · 2 ^ i` with `i = u.length` and `A_{i+1} = ones u + 1`: maximising the
weight is exactly minimising `A_{i+1} − i·log₃2`. -/
theorem term_disc_identity (u v : List Nat) :
    3 ^ (ones u + 1) * (2 ^ u.length * 3 ^ ones v)
      = 3 ^ ones (u ++ 1 :: v) * 2 ^ u.length := by
  have h1 : ones (u ++ 1 :: v) = ones u + (1 + ones v) := by
    rw [ones_append, ones_cons, if_pos rfl]
  rw [h1]
  have h2 : (3:Nat) ^ (ones u + (1 + ones v)) = 3 ^ (ones u + 1) * 3 ^ ones v := by
    rw [← Nat.pow_add]
    have : ones u + 1 + ones v = ones u + (1 + ones v) := by omega
    rw [this]
  rw [h2, Nat.mul_left_comm, Nat.mul_comm]

/-! ## Positivity, and the frozen regime -/

/-- The ground-state weight is positive as soon as the word has an odd letter. -/
theorem wTermMax_pos : ∀ w : List Nat, 0 < ones w → 0 < wTermMax w := by
  intro w
  induction w with
  | nil => intro h; simp [ones] at h
  | cons b t ih =>
      intro h
      rw [wTermMax_cons]
      by_cases hb : b = 1
      · rw [if_pos hb]
        have hp : 0 < (3:Nat) ^ ones t := Nat.pow_pos (by omega)
        have h8 : 3 ^ ones t ≤ Nat.max (3 ^ ones t) (2 * wTermMax t) :=
          Nat.le_max_left _ _
        omega
      · rw [if_neg hb]
        rw [ones_cons, if_neg hb, Nat.zero_add] at h
        have hi := ih h
        have h7 : Nat.max 0 (2 * wTermMax t) = 2 * wTermMax t :=
          Nat.max_eq_right (Nat.zero_le _)
        omega

/-! ## The consequence for the cycle half -/

/-- **The cycle minimum is pinned by the ground state.**  Through the cycle equation
`G · n = C`, the minimum element of a hypothetical cycle is determined to within a
factor `a` by the largest Boltzmann weight, i.e. by the minimum of the discrepancy
path.  A Class 1 quantity, proved to be one. -/
theorem cycle_ground_state {w : List Nat} {G n : Nat} (h : G * n = wC w) :
    wTermMax w ≤ G * n ∧ G * n ≤ ones w * wTermMax w := by
  rw [h]
  exact ⟨wTermMax_le_wC w, wC_le_ones_mul_max w⟩

/-- **No entropy in the pressure.**  Restated as a two-sided bound with the same
ground state on both sides: nothing separating the two is exponential in the length
of the word, so the pressure density of the partition function is zero. -/
theorem frozen (w : List Nat) :
    wTermMax w ≤ wC w ∧ wC w ≤ ones w * wTermMax w :=
  ⟨wTermMax_le_wC w, wC_le_ones_mul_max w⟩

/-- **`d`-covariance of the whole picture.**  Scaling the accumulator by `d` scales
the ground state by `d`, so the sandwich is invariant under `C ↦ d·C` and the
soundness filter applies verbatim.  Stated as the multiplicativity of the sandwich. -/
theorem sandwich_scales (d : Nat) (w : List Nat) :
    d * wTermMax w ≤ d * wC w ∧ d * wC w ≤ ones w * (d * wTermMax w) := by
  constructor
  · exact Nat.mul_le_mul_left _ (wTermMax_le_wC w)
  · have h := Nat.mul_le_mul_left d (wC_le_ones_mul_max w)
    have h2 : d * (ones w * wTermMax w) = ones w * (d * wTermMax w) := by
      rw [Nat.mul_left_comm]
    omega

end GroundState
end Collatz
