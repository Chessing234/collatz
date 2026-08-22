import Collatz.Structure.Divergence
import Collatz.Structure.OddRuns
import Collatz.Strategy.NeverDrops

/-!
# The arithmetic complexity of each half of the conjecture

This file records, as Lean propositions with the quantifier alternation left
visible in the statement, the exact position of the Collatz conjecture and of
each of its two halves in the arithmetical hierarchy.  Everything below is a
statement about *formulas*, not about numbers; the theorems are the equivalences
that justify each classification.

The classification, in one table (matrices are decidable in every case, so the
prefix is the whole story):

| statement                                        | form                       | class |
|--------------------------------------------------|----------------------------|-------|
| `CycleHalf` — every cycle is the trivial one     | `∀ m ∀ L (… → …)`          | `Π₁`  |
| `DivergenceHalf` — no orbit diverges             | `∀ n ∃ i ∃ L (…)`          | `Π₂`  |
| `Pi2Collatz` — the conjecture                    | `∀ n ∃ k (…)`              | `Π₂`  |
| `NoNeverDrops` — the `NeverDrops` reformulation  | `∀ x ∃ j (…)`              | `Π₂`  |
| `BoundedCollatz f` — with an explicit bound      | `∀ n ∃ k ≤ f n (…)`        | `Π₁`  |

Three consequences that are not recorded anywhere else in the development.

**1.  The divergence half is `Π₂`, not `Π₃`.**  `Structure.Divergence` states it
as `∀ n, ¬ Divergent n`, and `¬ Divergent n` unfolds to `∃ B ∀ i, orbit i n ≤ B`
— an honest `Σ₂` matrix, so that form of the sentence is `Π₃`.  But a
deterministic orbit is bounded exactly when it repeats a value, and "it repeats"
is `Σ₁`.  `divergenceHalf_of_pi3` and `collatz_iff_halves` below carry out the
replacement, and the whole conjecture then sits at `Π₂` with no slack.

**2.  The cycle half is `Π₁`, and that is a strong constraint.**  A `Π₁`
sentence is refuted by a single finite object (`cycleHalf_refuted_by_witness`),
which is why the computational assets of this project — the verified range, the
`L = 6809` frontier — are exactly the right shape for the cycle half and give
literally nothing for the divergence half, whose failure is not witnessed by any
finite object.  It also means that if the cycle half is independent of a `Σ₁`-sound
theory then it is *true*: a false `Π₁` sentence is refutable by evaluation.

**3.  The frontier programme is an ω-rule.**  `cycleHalf_iff_forall_bound` says
the cycle half is the conjunction over all `Lmax` of the finitary statements the
frontier files prove.  The conjunction is *true* as soon as every conjunct is
true, so the programme is sound; but no formal theory is closed under that
inference, so a proof of every conjunct is not a proof of the sentence unless it
is uniform in `Lmax`.  The frontier proofs in this repository take `Lmax` as a
numeral, so they are not uniform, and the ceiling is a matter of logic, not of
compute.  Worse, the instances are not cheap: `RealizableFrontier6809` derives
`L ≥ 6809` from the verified range `1 086 055`, and the table in `GapSandwich`
(`768 000 → 4701`, `1 086 055 → 6809`, `1 359 157 → 7863`) shows the frontier
growing linearly in the verified range, at roughly `L ≈ V / 160`.  So the `L`-th
instance of the ω-rule costs `Θ(L)` computation, and the programme is an
infinitary rule whose instances have unbounded cost — two independent reasons it
cannot terminate.

## What compactness gives, and what it does not

`nonDrop_scheme` below is the finite-satisfiability input to a compactness
argument: for every `L` there is a number greater than one whose accelerated
orbit does not drop below it for `L` steps, namely `2 ^ (L + 2) − 1`.  By
compactness of first-order logic the theory `PA + {"c does not drop for L
steps"}_{L ∈ ω}` is consistent, so some model of `PA` has an element `c` not
dropping for every *standard* number of steps; by overspill `c` does not drop for
some *nonstandard* number of steps either.

That is strictly weaker than a counterexample.  "`c` never drops" is the single
sentence `∀ j, c ≤ T^j c`, with `j` ranging over the model, and neither
compactness nor overspill delivers it: the scheme has one hypothesis per standard `L`,
and the sentence quantifies over all `L` of the model.  A model of `PA` with a
genuine nonstandard non-dropping element exists if and only if `PA` does not
prove the conjecture, so producing one is not a step towards a proof — it is
equivalent to an independence result.  This is the exact reason every
compactness or limit argument attempted in this project has been circular.
-/

namespace Collatz
namespace Complexity

open Reach Cycle Divergence OddRuns

/-! ## The two halves, with the prefix visible -/

/-- **`Π₁`.**  The cycle half: two universal quantifiers over a decidable
matrix.  Note that `Periodic m` is `Σ₁`, so the version in
`Structure.Divergence` prenexes to exactly this. -/
def CycleHalf : Prop :=
  ∀ m L : Nat, 0 < m → 0 < L → orbit L m = m → InTrivialCycle m

/-- **`Σ₁`.**  The orbit of `n` returns to a value it has already taken.  For a
deterministic map this is equivalent to boundedness, and unlike boundedness it
has no hidden universal quantifier. -/
def Repeats (n : Nat) : Prop := ∃ i L : Nat, 0 < L ∧ orbit (i + L) n = orbit i n

/-- **`Π₂`.**  The divergence half, with a `Σ₁` matrix. -/
def DivergenceHalf : Prop := ∀ n : Nat, 0 < n → Repeats n

/-- **`Π₃`.**  The divergence half as `Structure.Divergence` states it:
`∀ n ∃ B ∀ i`.  One quantifier higher than necessary. -/
def DivergenceHalfPi3 : Prop := ∀ n : Nat, 0 < n → ∃ B : Nat, ∀ i : Nat, orbit i n ≤ B

/-- **`Π₂`.**  The conjecture. -/
def Pi2Collatz : Prop := ∀ n : Nat, 0 < n → ∃ k : Nat, orbit k n = 1

/-- The `Π₂` form is definitionally the conjecture as stated in `Basic`. -/
theorem pi2Collatz_eq : Pi2Collatz = CollatzConjecture := rfl

/-! ## The `Π₃ → Π₂` reduction -/

/-- A bounded orbit repeats, so the `Π₃` form of the divergence half implies the
`Π₂` form.  (The converse also holds, but is not needed: it is the `Π₂` form
that we want, and dropping a quantifier is the useful direction.) -/
theorem divergenceHalf_of_pi3 (h : DivergenceHalfPi3) : DivergenceHalf := by
  intro n hn
  obtain ⟨B, hB⟩ := h n hn
  obtain ⟨i, L, hL, hrep⟩ := eventuallyPeriodic_of_bounded (n := n) ⟨B, hB⟩
  exact ⟨i, L, hL, hrep⟩

/-! ## `Π₂ ∧ Π₁ = Π₂`: the conjecture is the conjunction of the two halves -/

/-- From a repeat and the cycle half, the orbit reaches `1`. -/
theorem reachesOne_of_repeats_of_cycleHalf {n : Nat} (hn : 0 < n)
    (hrep : Repeats n) (hcyc : CycleHalf) : ReachesOne n := by
  obtain ⟨i, L, hL, hr⟩ := hrep
  have hm : 0 < orbit i n := orbit_positive hn i
  have hcy : orbit L (orbit i n) = orbit i n := by
    rw [← orbit_add L i n, Nat.add_comm L i]; exact hr
  have htriv : InTrivialCycle (orbit i n) := hcyc (orbit i n) L hm hL hcy
  have : ReachesOne (orbit i n) := reachesOne_of_inTrivialCycle htriv
  exact (reachesOne_iff_orbit i n).mpr this

/-- **The `Π₂` decomposition.**  Collatz is exactly `Π₂` divergence half plus
`Π₁` cycle half. -/
theorem collatz_of_halves (hdiv : DivergenceHalf) (hcyc : CycleHalf) :
    CollatzConjecture := by
  intro n hn
  exact reachesOne_of_repeats_of_cycleHalf hn (hdiv n hn) hcyc

/-- Collatz gives the `Π₂` divergence half: after reaching `1` the orbit repeats
with period three. -/
theorem divergenceHalf_of_collatz (h : CollatzConjecture) : DivergenceHalf := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  refine ⟨k, 3, by omega, ?_⟩
  rw [Nat.add_comm k 3, orbit_add 3 k n, hk]
  decide

/-- Collatz gives the `Π₁` cycle half. -/
theorem cycleHalf_of_collatz (h : CollatzConjecture) : CycleHalf := by
  intro m L hm hL hcy
  exact mem_trivial_of_periodic_of_reachesOne ⟨L, ⟨hL, hcy⟩⟩ (h m hm)

/-- **The exact decomposition.**  `Π₂ ↔ Π₂ ∧ Π₁`. -/
theorem collatz_iff_halves : CollatzConjecture ↔ (DivergenceHalf ∧ CycleHalf) :=
  ⟨fun h => ⟨divergenceHalf_of_collatz h, cycleHalf_of_collatz h⟩,
   fun h => collatz_of_halves h.1 h.2⟩

/-! ## Where the `Π₂` really lives: the Skolem function

The single existential of `Pi2Collatz` is witnessed by the total stopping time.
Bounding it by any explicit function collapses the conjecture to `Π₁`, since the
existential becomes bounded.  This is the precise sense in which "find an
effective bound on the stopping time" and "prove the conjecture" differ: they
differ by one quantifier, and by nothing else. -/

/-- **`Π₁`.**  The conjecture with an explicit bound on the stopping time.  The
existential is bounded, so for elementary `f` this is a `Π₁` sentence. -/
def BoundedCollatz (f : Nat → Nat) : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, k ≤ f n ∧ orbit k n = 1

/-- Any explicit bound proves the conjecture; the content of the conjecture is
exactly the missing bound. -/
theorem collatz_of_bounded {f : Nat → Nat} (h : BoundedCollatz f) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨k, _, hk⟩ := h n hn
  exact ⟨k, hk⟩

/-- Conversely a bound is not free: `BoundedCollatz f` for a *given* `f` is a
genuinely stronger statement, and the conjecture only supplies `f` after an
unbounded search.  Recorded here as the one-line implication that does hold. -/
theorem bounded_of_collatz_at {f : Nat → Nat} {n : Nat} (hn : 0 < n)
    (h : CollatzConjecture) (hf : ∀ k, orbit k n = 1 → k ≤ f n) :
    ∃ k : Nat, k ≤ f n ∧ orbit k n = 1 := by
  obtain ⟨k, hk⟩ := h n hn
  exact ⟨k, hf k hk, hk⟩

/-! ## The `NeverDrops` reformulation is the same `Π₂` with a smaller witness

`NeverDrops.collatz_iff_neverDrops` reformulates the conjecture as "`1` is the
only number that never drops".  Negated and prenexed that is `∀ x ∃ j`, the same
`Π₂` prefix as `Pi2Collatz` — the reformulation does not lower the complexity.
What it does lower is the Skolem function: the witness is the *first descent
time* rather than the total stopping time.  Both are `Π₂`; the reformulation is
a reduction of witness size, not of quantifier alternation, and no argument that
turns on alternation can benefit from it. -/

/-- **`Π₂`.**  The `NeverDrops` form: every number above one eventually drops
below itself. -/
def NoNeverDrops : Prop :=
  ∀ x : Nat, 1 < x → ∃ j : Nat, acceleratedOrbit j x < x

/-- The `NeverDrops` form has the same `Π₂` prefix and is equivalent to the
conjecture. -/
theorem collatz_iff_noNeverDrops : CollatzConjecture ↔ NoNeverDrops := by
  rw [NeverDrops.collatz_iff_neverDrops]
  constructor
  · intro h x hx
    by_cases hnd : NeverDrops.NeverDrops x
    · exact absurd (h x hnd) (by omega)
    · unfold NeverDrops.NeverDrops at hnd
      by_cases hex : ∃ j : Nat, acceleratedOrbit j x < x
      · exact hex
      · exact absurd (fun j => Nat.le_of_not_lt (fun hc => hex ⟨j, hc⟩)) hnd
  · intro h x hnd
    by_cases hx : 1 < x
    · obtain ⟨j, hj⟩ := h x hx
      exact absurd (hnd j) (by omega)
    · omega

/-! ## `Π₁` has finite refutations; `Π₂` does not -/

/-- **A single finite object refutes the cycle half.**  This is what `Π₁` means,
and it is why every computational asset in this project bears on the cycle half
and on nothing else. -/
theorem cycleHalf_refuted_by_witness {m L : Nat} (hm : 0 < m) (hL : 0 < L)
    (hcy : orbit L m = m) (hnt : ¬ InTrivialCycle m) : ¬ CycleHalf :=
  fun h => hnt (h m L hm hL hcy)

/-- The frontier statement: no nontrivial cycle of length at most `Lmax`.  Each
of these is a finitary theorem; the repository proves them for `Lmax` up to the
current frontier. -/
def CycleHalfUpTo (Lmax : Nat) : Prop :=
  ∀ m L : Nat, 0 < m → 0 < L → L ≤ Lmax → orbit L m = m → InTrivialCycle m

/-- **The frontier programme is an ω-rule.**  The cycle half is the conjunction
of all the frontier statements.  The equivalence is trivial mathematically and
that is the point: truth of every conjunct gives truth of the sentence, but
provability of every conjunct does not give provability of the sentence in any
formal theory, because no formal theory is closed under an infinitary rule.  A
proof uniform in `Lmax` is required, and the numeral-indexed frontier proofs are
not uniform. -/
theorem cycleHalf_iff_forall_bound : CycleHalf ↔ ∀ Lmax : Nat, CycleHalfUpTo Lmax :=
  ⟨fun h _Lmax m L hm hL _ hcy => h m L hm hL hcy,
   fun h m L hm hL hcy => h L m L hm hL (Nat.le_refl L) hcy⟩

/-! ## The compactness input, formalised

An odd number does not decrease under the accelerated map, so a number that
opens with a run of `L` odd steps does not drop for `L` steps.  `2 ^ (L+2) − 1`
opens with `L + 2` odd steps, which supplies one witness for every `L`: exactly
the finite satisfiability that a compactness argument consumes, and exactly the
reason such an argument yields nothing. -/

/-- The accelerated map does not decrease an odd number. -/
theorem le_acceleratedStep_of_odd {x : Nat} (hx : x % 2 = 1) :
    x ≤ acceleratedStep x := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- Along an odd run the accelerated orbit is nondecreasing from the start. -/
theorem le_acceleratedOrbit_of_oddRun {x j : Nat} (h : OddRun x j) :
    ∀ i : Nat, i ≤ j → x ≤ acceleratedOrbit i x := by
  have key : ∀ i : Nat, i ≤ j → x ≤ acceleratedOrbit i x := by
    intro i
    induction i with
    | zero => intro _; exact Nat.le_refl x
    | succ i ih =>
      intro hij
      have hi : i ≤ j := by omega
      have hlt : i < j := by omega
      have hodd : acceleratedOrbit i x % 2 = 1 := h i hlt
      have hstep : acceleratedOrbit i x ≤ acceleratedStep (acceleratedOrbit i x) :=
        le_acceleratedStep_of_odd hodd
      have hnext : acceleratedOrbit (i + 1) x = acceleratedStep (acceleratedOrbit i x) :=
        acceleratedOrbit_succ_step i x
      rw [hnext]
      exact Nat.le_trans (ih hi) hstep
  exact key

/-- **The finite-satisfiability scheme.**  For every `L` there is a number
greater than one whose accelerated orbit does not drop below it for `L` steps.
Every finite fragment of "`c` never drops" is satisfiable in the standard model,
so compactness makes the whole scheme consistent with `PA`; and the resulting
nonstandard element is not a counterexample, because "never drops" is a single
sentence quantifying over all steps of the model, not a scheme. -/
theorem nonDrop_scheme (L : Nat) :
    ∃ x : Nat, 1 < x ∧ ∀ j : Nat, j ≤ L → x ≤ acceleratedOrbit j x := by
  refine ⟨2 ^ (L + 2) - 1, ?_, ?_⟩
  · have h4 : (2:Nat) ^ (L + 2) = 2 ^ L * 4 := by rw [Nat.pow_add]
    have hpos : 0 < (2:Nat) ^ L := Arith.two_pow_pos L
    omega
  · intro j hj
    exact le_acceleratedOrbit_of_oddRun (oddRun_two_pow_sub_one (L + 2)) j (by omega)

end Complexity
end Collatz
