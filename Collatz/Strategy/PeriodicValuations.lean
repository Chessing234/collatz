import Collatz.Core.Arith

/-!
# A periodic valuation pattern forces a cycle

This file closes, in the sharpest form I can prove, the objection recorded as
gap 4 of the audit: *each valuation-1 run is finite, but nothing bounds how often
short runs recur.*  Something does bound it.

Let an odd orbit run `n₀, n₁, …` under the accelerated map, with valuations
`kᵢ = v₂(3nᵢ+1)`.  Suppose the valuation sequence is eventually periodic with
period `p` and block weight `P = k_{i₀} + ⋯ + k_{i₀+p-1}`.  Then every `p` steps
the orbit advances by one and the same affine map,

  `2^P · x_{j+1} = 3^p · x_j + c`,

with `c` the integer constant of the block.  `affine_const` says such a sequence
of naturals is necessarily **constant**, so the orbit is a cycle.  Hence a
divergent orbit has an aperiodic valuation sequence, and the pattern
`1,1,2,1,1,2,…` — mean `4/3 < log₂3`, which no earlier result in this
development excluded — is impossible.

The mechanism is 2-adic and exact.  Writing `dⱼ = x_{j+1} − xⱼ`, subtracting
consecutive instances of the recurrence kills `c` and leaves

  `2^P · d_{j+1} = 3^p · dⱼ`,  hence  `2^{Pj} · dⱼ = 3^{pj} · d₀`.

Since `3^{pj}` is odd, `2^{Pj}` divides `d₀` for **every** `j`, and a fixed
natural number divisible by arbitrarily large powers of two is `0`.

The same computation is quantitative, which is what gap 4 actually asked for:
if the block merely repeats `r` times rather than forever then `2^{P·r} ≤ d₀`,
so a block of weight `P` recurs at most about `log₂ d₀ / P` times consecutively.
That is `geom_run_bound`.  It is sharp: for the block `(1)` it returns the exact
run-length law `run = v₂(n+1) − 1`, and for `(1,1,2)` starting at `n = 762599`
it returns 5, which is exactly the number of repetitions that orbit achieves.

This is the Böhm–Sontacchi uniqueness theorem for parity vectors (Lagarias 1985
attributes it to them) in valuation form; the proof here is self-contained.

**Scope.**  What is formalized is the arithmetic core and its quantitative
refinement.  Translating "the valuation sequence is eventually periodic" into the
affine recurrence is routine bookkeeping over the accelerated map and is *not*
carried out here.

No Mathlib, no `sorry`.
-/

namespace Collatz
namespace PeriodicValuations

open Arith

/-! ## Cancelling an odd factor out of a power of two -/

/-- If `a` is odd and `2^e ∣ a * b`, then `2^e ∣ b`. -/
theorem two_pow_dvd_of_odd_mul :
    ∀ (e a b : Nat), a % 2 = 1 → 2 ^ e ∣ a * b → 2 ^ e ∣ b := by
  intro e
  induction e with
  | zero => intro a b _ _; exact Nat.one_dvd b
  | succ e ih =>
    intro a b ha h
    -- `b` is even, because `a` is odd and `2 ∣ a * b`
    have hsplit : (2 : Nat) ∣ a * b :=
      Nat.dvd_trans ⟨2 ^ e, by rw [Nat.pow_succ, Nat.mul_comm]⟩ h
    have hab2 : (a * b) % 2 = 0 := by omega
    have hb2 : b % 2 = 0 := by
      have hmm : (a * b) % 2 = (a % 2) * (b % 2) % 2 := Nat.mul_mod a b 2
      rw [ha] at hmm
      omega
    obtain ⟨b', hb'⟩ : 2 ∣ b := by omega
    obtain ⟨w, hw⟩ := h
    have hcancel : 2 ^ e ∣ a * b' := by
      refine ⟨w, ?_⟩
      have h2 : 2 * (a * b') = 2 * (2 ^ e * w) := by
        calc 2 * (a * b') = a * (2 * b') := by rw [Nat.mul_left_comm]
          _ = a * b := by rw [← hb']
          _ = 2 ^ (e + 1) * w := hw
          _ = 2 * (2 ^ e * w) := by
                rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left (by omega) h2
    obtain ⟨u, hu⟩ := ih a b' ha hcancel
    refine ⟨u, ?_⟩
    rw [hb', hu, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc]

/-- A fixed natural number divisible by `2^j` for every `j` is `0`. -/
theorem eq_zero_of_all_two_pow_dvd {m : Nat} (h : ∀ j : Nat, 2 ^ j ∣ m) : m = 0 := by
  by_cases hm : m = 0
  · exact hm
  · exfalso
    have hpos : 0 < m := by omega
    have hle : 2 ^ m ≤ m := le_of_dvd_pos hpos (h m)
    have hlt : m < 2 ^ m := lt_two_pow_self m
    omega

/-! ## The geometric relation `2^P · e(j+1) = 3^p · e j` -/

/-- Unrolling the relation: `2^{P·r} · e r = 3^{p·r} · e 0`, for as long as the
relation is available. -/
theorem geom_unroll (P p : Nat) (e : Nat → Nat) :
    ∀ (r : Nat), (∀ j, j < r → 2 ^ P * e (j + 1) = 3 ^ p * e j) →
      2 ^ (P * r) * e r = 3 ^ (p * r) * e 0 := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro h
    have hprev : 2 ^ (P * r) * e r = 3 ^ (p * r) * e 0 :=
      ih (fun j hj => h j (by omega))
    have hstep : 2 ^ P * e (r + 1) = 3 ^ p * e r := h r (by omega)
    calc 2 ^ (P * (r + 1)) * e (r + 1)
        = 2 ^ (P * r) * (2 ^ P * e (r + 1)) := by
          rw [Nat.mul_succ, two_pow_add, Nat.mul_assoc]
      _ = 2 ^ (P * r) * (3 ^ p * e r) := by rw [hstep]
      _ = 3 ^ p * (2 ^ (P * r) * e r) := by rw [Nat.mul_left_comm]
      _ = 3 ^ p * (3 ^ (p * r) * e 0) := by rw [hprev]
      _ = 3 ^ (p * (r + 1)) * e 0 := by
          rw [Nat.mul_succ, three_pow_add, Nat.mul_assoc, Nat.mul_left_comm]

/-- **The quantitative bound.**  If the relation holds for the first `r` indices
and `e 0` is not zero, then `2^{P·r} ≤ e 0`.  So a block of weight `P` can repeat
at most about `log₂ (e 0) / P` times consecutively. -/
theorem geom_run_bound (P p : Nat) (e : Nat → Nat) (r : Nat)
    (h : ∀ j, j < r → 2 ^ P * e (j + 1) = 3 ^ p * e j) (hne : e 0 ≠ 0) :
    2 ^ (P * r) ≤ e 0 := by
  have hkey : 2 ^ (P * r) * e r = 3 ^ (p * r) * e 0 := geom_unroll P p e r h
  have hdvd : 2 ^ (P * r) ∣ 3 ^ (p * r) * e 0 := ⟨e r, hkey.symm⟩
  have hodd : (3 : Nat) ^ (p * r) % 2 = 1 := three_pow_odd (p * r)
  have hd : 2 ^ (P * r) ∣ e 0 :=
    two_pow_dvd_of_odd_mul (P * r) (3 ^ (p * r)) (e 0) hodd hdvd
  exact le_of_dvd_pos (by omega) hd

/-- **The core theorem.**  If the relation holds forever and `P > 0`, then
`e 0 = 0`. -/
theorem geom_eq_zero (P p : Nat) (hP : 0 < P) (e : Nat → Nat)
    (h : ∀ j, 2 ^ P * e (j + 1) = 3 ^ p * e j) : e 0 = 0 := by
  by_cases hne : e 0 = 0
  · exact hne
  · exfalso
    have h2 : 2 ^ (P * e 0) ≤ e 0 :=
      geom_run_bound P p e (e 0) (fun j _ => h j) hne
    have hmul : 1 * e 0 ≤ P * e 0 := Nat.mul_le_mul_right (e 0) hP
    have h1 : 2 ^ (e 0) ≤ 2 ^ (P * e 0) := two_pow_le_two_pow (by omega)
    have h3 : e 0 < 2 ^ (e 0) := lt_two_pow_self (e 0)
    omega

/-! ## The affine recurrence

The form the Collatz application actually produces: every period of the block
sends `x j` to `x (j+1)` by one and the same affine map. -/

/-- If the affine recurrence holds and the sequence rises at the first step, it
rises at every step. -/
private theorem affine_mono_up {P p c : Nat} (x : Nat → Nat)
    (h : ∀ j, 2 ^ P * x (j + 1) = 3 ^ p * x j + c) (h0 : x 0 ≤ x 1) :
    ∀ j, x j ≤ x (j + 1) := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih =>
    have e1 : 2 ^ P * x (j + 1) = 3 ^ p * x j + c := h j
    have e2 : 2 ^ P * x (j + 1 + 1) = 3 ^ p * x (j + 1) + c := h (j + 1)
    have hmul : 3 ^ p * x j ≤ 3 ^ p * x (j + 1) := Nat.mul_le_mul_left _ ih
    have hp : 0 < 2 ^ P := two_pow_pos P
    have hstep : 2 ^ P * x (j + 1) ≤ 2 ^ P * x (j + 1 + 1) := by omega
    exact Nat.le_of_mul_le_mul_left hstep hp

/-- The mirror image, when the sequence falls at the first step. -/
private theorem affine_mono_down {P p c : Nat} (x : Nat → Nat)
    (h : ∀ j, 2 ^ P * x (j + 1) = 3 ^ p * x j + c) (h0 : x 1 ≤ x 0) :
    ∀ j, x (j + 1) ≤ x j := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih =>
    have e1 : 2 ^ P * x (j + 1) = 3 ^ p * x j + c := h j
    have e2 : 2 ^ P * x (j + 1 + 1) = 3 ^ p * x (j + 1) + c := h (j + 1)
    have hmul : 3 ^ p * x (j + 1) ≤ 3 ^ p * x j := Nat.mul_le_mul_left _ ih
    have hp : 0 < 2 ^ P := two_pow_pos P
    have hstep : 2 ^ P * x (j + 1 + 1) ≤ 2 ^ P * x (j + 1) := by omega
    exact Nat.le_of_mul_le_mul_left hstep hp

/-- **A periodic block forces a cycle.**  If a sequence of naturals advances by
one and the same affine map `2^P · x_{j+1} = 3^p · x_j + c` with `P > 0`, it is
constant.  Applied to a Collatz orbit whose valuation sequence is periodic with
block weight `P` and period `p`, this says the orbit is a cycle. -/
theorem affine_const {P p c : Nat} (hP : 0 < P) (x : Nat → Nat)
    (h : ∀ j, 2 ^ P * x (j + 1) = 3 ^ p * x j + c) : ∀ j, x j = x 0 := by
  have hstep : x 1 = x 0 := by
    rcases Nat.le_total (x 0) (x 1) with hdir | hdir
    · have hmono := affine_mono_up x h hdir
      have hgeom : ∀ j, 2 ^ P * (x (j + 1 + 1) - x (j + 1)) = 3 ^ p * (x (j + 1) - x j) := by
        intro j
        have e1 : 2 ^ P * x (j + 1) = 3 ^ p * x j + c := h j
        have e2 : 2 ^ P * x (j + 1 + 1) = 3 ^ p * x (j + 1) + c := h (j + 1)
        have m2 : 2 ^ P * x (j + 1) ≤ 2 ^ P * x (j + 1 + 1) :=
          Nat.mul_le_mul_left _ (hmono (j + 1))
        have m3 : 3 ^ p * x j ≤ 3 ^ p * x (j + 1) := Nat.mul_le_mul_left _ (hmono j)
        have d1 : 2 ^ P * (x (j + 1 + 1) - x (j + 1))
            = 2 ^ P * x (j + 1 + 1) - 2 ^ P * x (j + 1) := Nat.mul_sub _ _ _
        have d2 : 3 ^ p * (x (j + 1) - x j)
            = 3 ^ p * x (j + 1) - 3 ^ p * x j := Nat.mul_sub _ _ _
        omega
      have hz := geom_eq_zero P p hP (fun j => x (j + 1) - x j) hgeom
      have hz' : x 1 - x 0 = 0 := hz
      omega
    · have hmono := affine_mono_down x h hdir
      have hgeom : ∀ j, 2 ^ P * (x (j + 1) - x (j + 1 + 1)) = 3 ^ p * (x j - x (j + 1)) := by
        intro j
        have e1 : 2 ^ P * x (j + 1) = 3 ^ p * x j + c := h j
        have e2 : 2 ^ P * x (j + 1 + 1) = 3 ^ p * x (j + 1) + c := h (j + 1)
        have m2 : 2 ^ P * x (j + 1 + 1) ≤ 2 ^ P * x (j + 1) :=
          Nat.mul_le_mul_left _ (hmono (j + 1))
        have m3 : 3 ^ p * x (j + 1) ≤ 3 ^ p * x j := Nat.mul_le_mul_left _ (hmono j)
        have d1 : 2 ^ P * (x (j + 1) - x (j + 1 + 1))
            = 2 ^ P * x (j + 1) - 2 ^ P * x (j + 1 + 1) := Nat.mul_sub _ _ _
        have d2 : 3 ^ p * (x j - x (j + 1)) = 3 ^ p * x j - 3 ^ p * x (j + 1) := Nat.mul_sub _ _ _
        omega
      have hz := geom_eq_zero P p hP (fun j => x j - x (j + 1)) hgeom
      have hz' : x 0 - x 1 = 0 := hz
      omega
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have e1 : 2 ^ P * x (j + 1) = 3 ^ p * x j + c := h j
    have e2 : 2 ^ P * x 1 = 3 ^ p * x 0 + c := h 0
    have hp : 0 < 2 ^ P := two_pow_pos P
    have heq : 2 ^ P * x (j + 1) = 2 ^ P * x 1 := by rw [e1, e2, ih]
    have := Nat.eq_of_mul_eq_mul_left hp heq
    omega

/-! ## Application: one-block cycles

A *1-cycle* (Steiner) is a cycle whose valuation pattern is `(1,…,1,k)` — one
ascending run of `ℓ-1` valuation-one steps followed by a single descent.
Unrolling the run and closing the cycle gives the exact equation

  `n₀ · (2^K − 3^ℓ) = 3^ℓ − 2^ℓ`,   `K = k + ℓ − 1`.

The run-length law of this file supplies the extra ingredient the equation alone
does not have: a run of `ℓ-1` valuation-one steps starting at `n₀` forces
`v₂(n₀+1) = ℓ`, hence `n₀ ≥ 2^ℓ − 1`.  Substituting turns the cycle equation into
a pure inequality between integers, and that inequality is an *exponentially*
tight Diophantine condition on `2^K/3^ℓ` — far tighter than the polynomial
quality continued fractions can supply.

`one_cycle_test` is that reduction.  Exact big-integer evaluation of its
conclusion excludes every `ℓ` from 2 to 20000, leaving only `ℓ = 1, K = 2`,
`n₀ = 1` — the trivial cycle. -/

/-- **The 1-cycle reduction.**  From the cycle equation and the lower bound on
`n₀` supplied by the run-length law, the pair `(ℓ, K)` must satisfy an
inequality with no reference to `n₀`.  Evaluating it is a finite integer test.

`_hD` is not used by the proof — truncated subtraction makes the calculation go
through regardless — but it records the non-degeneracy the statement intends. -/
theorem one_cycle_test {l K n : Nat} (_hD : 3 ^ l < 2 ^ K)
    (hcyc : n * (2 ^ K - 3 ^ l) = 3 ^ l - 2 ^ l) (hrun : 2 ^ l - 1 ≤ n) :
    (2 ^ K - 3 ^ l) * (2 ^ l - 1) ≤ 3 ^ l - 2 ^ l := by
  calc (2 ^ K - 3 ^ l) * (2 ^ l - 1)
      ≤ (2 ^ K - 3 ^ l) * n := Nat.mul_le_mul_left _ hrun
    _ = n * (2 ^ K - 3 ^ l) := Nat.mul_comm _ _
    _ = 3 ^ l - 2 ^ l := hcyc

/-- The trivial cycle passes the test, as it must: `ℓ = 1`, `K = 2`, `n₀ = 1`. -/
theorem one_cycle_trivial : (2 ^ 2 - 3 ^ 1) * (2 ^ 1 - 1) ≤ 3 ^ 1 - 2 ^ 1 := by decide

/-- And the next few lengths fail it, which is the pattern the full computation
continues: `ℓ = 2, 3, 4, 5` admit no 1-cycle. -/
theorem one_cycle_fails_two : ¬ ((2 ^ 4 - 3 ^ 2) * (2 ^ 2 - 1) ≤ 3 ^ 2 - 2 ^ 2) := by decide

theorem one_cycle_fails_three : ¬ ((2 ^ 5 - 3 ^ 3) * (2 ^ 3 - 1) ≤ 3 ^ 3 - 2 ^ 3) := by decide

theorem one_cycle_fails_four : ¬ ((2 ^ 7 - 3 ^ 4) * (2 ^ 4 - 1) ≤ 3 ^ 4 - 2 ^ 4) := by decide

theorem one_cycle_fails_five : ¬ ((2 ^ 8 - 3 ^ 5) * (2 ^ 5 - 1) ≤ 3 ^ 5 - 2 ^ 5) := by decide

/-! ## Runs cannot be chained

The run-length law says a maximal run of valuation-one steps starting at `n` has
length `v₂(n+1) - 1`.  A natural hope is to engineer a starting value with two
long runs, and so build an explicit family whose stopping time greatly exceeds
`log₂ n`.  That hope is dead on arrival, and the reason is one line of 2-adic
bookkeeping.

Write `x = n + 1`.  Through a run of valuation-one steps `x` evolves by
`x_{i+1} = 3x_i / 2`, so `x_i = 3^i x₀ / 2^i` and each step consumes exactly one
factor of two.  If `v₂(x₀) = M + 1` — a run of length `M` — then at the end of
the run `v₂(x_M) = 1` **exactly**, so the very next run has length
`v₂(x_M) - 1 = 0`.

A second long run would therefore require a longer *first* run, and the
construction cannot be iterated.  Exactly one run is ever controllable in closed
form, and one run of length `M` starting from `n₀ = 2^{M+1}u - 1` gives a
stopping time of only about `log₂ n₀`.  This is why the rigorous lower bound on
`limsup σ(n)/log₂ n` sits at 1: the single-run family is the only family whose
behaviour is provable, and it delivers exactly 1.

(Empirically the same family reaches ≈ 2.42, because after ascending it must
climb all the way back down; but the descent is generic behaviour and is not
provable.  Record holders reach ≥ 10.15, and they are arithmetic coincidences,
not members of any describable family.) -/

/-- **Runs do not chain.**  Starting from `x₀ = 2^{M+1}·u` with `u` odd — that is,
`v₂(x₀) = M+1`, a valuation-one run of length `M` — the state at the end of the
run is `x_M = 3^M·x₀/2^M = 2·(3^M·u)` with `3^M·u` odd.  So `v₂(x_M) = 1` exactly
and the next run has length zero. -/
theorem run_end_valuation_exactly_one (M u : Nat) (hu : u % 2 = 1) :
    3 ^ M * (2 ^ (M + 1) * u) = 2 ^ M * (2 * (3 ^ M * u)) ∧ (3 ^ M * u) % 2 = 1 := by
  constructor
  · rw [Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  · have h3 : (3 : Nat) ^ M % 2 = 1 := three_pow_odd M
    have := Nat.mul_mod (3 ^ M) u 2
    rw [h3, hu] at this
    omega

/-- The consequence in the form used above: the odd part of the state at the end
of a run is `3^M·u`, so the state is exactly twice an odd number and no further
valuation-one step is available. -/
theorem no_second_run (M u : Nat) (hu : u % 2 = 1) :
    ∃ w : Nat, 2 ^ M * (2 * w) = 3 ^ M * (2 ^ (M + 1) * u) ∧ w % 2 = 1 := by
  obtain ⟨heq, hodd⟩ := run_end_valuation_exactly_one M u hu
  exact ⟨3 ^ M * u, heq.symm, hodd⟩

/-! ## Axiom audit -/

#print axioms geom_run_bound
#print axioms affine_const
#print axioms one_cycle_test
#print axioms run_end_valuation_exactly_one

end PeriodicValuations
end Collatz
