import Collatz.Strategy.ScaleLadder
import Collatz.Structure.AccCycle

/-!
# Round XI, Sections XXI–XXIV — the fibre interaction, and why it is empty

The round's central conditional was

> `CycleCriterion` (`G ∣ C`) **+** `coupling_bound` ⟹ a *stronger* coupling bound,

with the intuition that the divisibility condition might eliminate exactly the words
for which the coupling is weakest.  This file reports the outcome.  **The bridge
exists, it is one inequality, and it does not self-strengthen.**  Everything below is
the negative half; the positive half is stated and then handed to the file that
proved it first.

## What the bridge is, and who owns it

Generalising `ScaleLadder.coupling_bound` from the floor `2 ^ k` to a free floor `c`
(the induction never uses that the floor is a power of two), applying it at the cycle
minimum, and substituting `G ∣ C` gives

> `3 · n · (2 ^ L − 3 ^ a) ≤ a · 2 ^ L`.

I derived this independently and then found it already proved, in this same round, as
`SegmentMonoid.cycle_frontier` (with `SegmentMonoid.floor_coupling` the free-floor
generalisation).  My duplicate of all three statements is deleted rather than kept as
a second entry point — the index exists to catch exactly this.  What is recorded here
is the measurement I ran on it and the three negative results the other route did not
cover.

COMPUTATIONAL (exact integers, `a = ⌊L·log₃2⌋` — the only `a` that can pass, since a
smaller `a` enlarges the gap and shrinks the count — verified range `n ≥ 1 086 464`):

| bound | constant | first surviving `(L, a)` |
|---|---|---|
| `CycleProduct.cycle_min_bound` | `n·g ≤ 2a·3^a` | `(1539, 971)` |
| `coupling_bound` at a floor `2 ^ k ≤ n` | `3·2^k·g ≤ a·2^L` | `(2593, 1636)` |
| free floor `c = n` (`cycle_frontier`) | `3·n·g ≤ a·2^L` | `(4701, 2966)` |

Threefold improvement in reach over the product method, and it still lands *below*
`RealizableFrontier6809`.  The bridge adds no frontier.

## Result 1 — why it cannot be self-strengthened (the arrow that fails)

Every bound in that table uses one and only one inequality about orbit values,
`n ≤ x_t`.  The obvious sharpening is the ordering bound `FloorSchedule.pin_lower`,

`3 ^ (A t) · n ≤ 2 ^ t · x_t`,  i.e.  `x_t ≥ n · 3 ^ (A t) / 2 ^ t`,

strictly better than `x_t ≥ n` at every heavy prefix.  Substituting it into the exact
closure identity `∏_t (1 + 1/(3 x_t)) = 2 ^ L / 3 ^ a` gives

`Σ_t 2 ^ t / (3 · 3 ^ (A t) · n)  =  C / (3 ^ a · n)  =  g / 3 ^ a`,

because `Σ_t 3 ^ (a − 1 − A t) · 2 ^ t` **is** `C` — the closed form of `affineC`.
So the sharpened inequality reads `log(1 + g/3^a) ≤ g/3^a`: a **tautology**.
MATHEMATICALLY_PROVED, and verified in exact rationals on eleven genuine cycles of
`3x+d`, `d = 1, 5, 7, 13, 59, −1` — equality in every case, no rounding.

The reason is structural, and it is this file's main claim:

> `2 ^ t · x_t = 3 ^ (A t) · n + C_t` is an **identity**: every orbit value of a cycle
> is an exact function of `(word, n)`.  Hence every lower bound on `x_t` is either the
> identity itself — which returns the cycle equation and nothing else — or the external
> input `x_t ≥ n`.  There is no third source.  The coupling therefore contains exactly
> the information `G ∣ C` contains, and the conditional
> "`G ∣ C` + coupling ⟹ stronger coupling" fails **by degeneracy, not by difficulty**.

This is visible in Lean without any new proof: this round's
`CouplingNormal.cycle_total_coupling` — "the total coupling around a cycle is
`2^L/3^a`" — is discharged by `exact (cycle_affine h).symm`.  The closure identity
*is* the cycle equation, not an extra condition on it.

## Result 2 — the ordering restriction `G ∣ C` imposes, and its vacuity

`prefix_gap` is the exact ordering consequence of `G ∣ C` read at the cycle minimum:
for every prefix `j`,

`2 ^ j · C ≤ 3 ^ (A j) · C + g · C_j`,   equivalently  `C_j / C ≥ (2^j − 3^(A j)) / g`.

`prefix_gap_of_heavy` proves the same conclusion from heaviness `2 ^ j ≤ 3 ^ (A j)`
alone, **with no cycle hypothesis at all** — the right-hand side already dominates.
And `prefix_gap_at_L` shows the one prefix where heaviness is unavailable, `j = L`, is
an *equality*: the cycle equation restated.  Measured: the cycle minimum's word is
heavy at every proper prefix on all eleven genuine cycles above.  So

> **`G ∣ C` restricts the ordered odd-step times strictly *less* than ordinary
> heaviness does.**

That answers Round VIII's question in the negative from the other side: the coupling
machinery cannot consume the ordering, because `G ∣ C` does not constrain it.

## Result 3 — the divergence-half filter is vacuous on the cycle criterion

`expStep_no_ledge`: a window with the odd count saturated (`oddCount x j = j`, the
defining property of Round X's witness `expStep`) has `2 ^ j < 3 ^ j` for `j ≥ 1`, so
`CycleCriterion`'s hypothesis `3 ^ a < 2 ^ L` is **unsatisfiable**.  Hence
"`G ∣ C` ⟹ `expStep` contradiction" is true and certifies nothing: the ledge condition
consumes `oddCount < j` in its very statement (`oddCount_lt_of_ledge`).  The
divergence-half filter cannot validate cycle-half work — the exact dual of `CLOSURE.md`
diagnostic 4, and it is worth recording as such, because the brief asked for that
statement as a tractable sub-target and it turns out to be tractable only because it is
empty.
-/

namespace Collatz
namespace CoupledCycle

open Reach AffineExact AccCycle

/-! ## The ordering restriction imposed by `G ∣ C` -/

/-- **The prefix inequality: the exact ordering restriction `G ∣ C` imposes.**
At every prefix `j` of a cycle read from its minimum,

`2 ^ j · C ≤ 3 ^ (A j) · C + g · C_j`.

It says the partial accumulator cannot fall behind the partial gap — equivalently,
that this rotation is the minimal one.  The gap is carried as a free variable `g` with
`C = g · n`, which is `G ∣ C` and keeps the statement free of truncated subtraction. -/
theorem prefix_gap {n L g : Nat} (hmin : ∀ t : Nat, n ≤ acceleratedOrbit t n)
    (hg : affineC L n = g * n) (j : Nat) :
    2 ^ j * affineC L n ≤ 3 ^ oddCount n j * affineC L n + g * affineC j n := by
  have hx : n ≤ acceleratedOrbit j n := hmin j
  have haff := affine_exact n j
  have hstep : 2 ^ j * n ≤ 3 ^ oddCount n j * n + affineC j n := by
    have h1 : 2 ^ j * n ≤ 2 ^ j * acceleratedOrbit j n := Nat.mul_le_mul_left _ hx
    omega
  have hmul : g * (2 ^ j * n) ≤ g * (3 ^ oddCount n j * n + affineC j n) :=
    Nat.mul_le_mul_left _ hstep
  have eL : g * (2 ^ j * n) = 2 ^ j * (g * n) := by
    rw [Nat.mul_left_comm]
  have eR : g * (3 ^ oddCount n j * n + affineC j n)
      = 3 ^ oddCount n j * (g * n) + g * affineC j n := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [eL, eR] at hmul
  rw [hg]
  exact hmul

/-- **The prefix inequality is implied by heaviness, with no cycle hypothesis.**
So `G ∣ C` restricts the ordering strictly *less* than ordinary heaviness does: at
every heavy prefix the constraint is already satisfied for free, for every `g`, every
`n` and every `L`. -/
theorem prefix_gap_of_heavy {n L g j : Nat} (hheavy : 2 ^ j ≤ 3 ^ oddCount n j) :
    2 ^ j * affineC L n ≤ 3 ^ oddCount n j * affineC L n + g * affineC j n := by
  have h1 : 2 ^ j * affineC L n ≤ 3 ^ oddCount n j * affineC L n :=
    Nat.mul_le_mul_right _ hheavy
  omega

/-- At the closing index `j = L` — the one prefix where heaviness is unavailable,
since `3 ^ a < 2 ^ L` is the ledge — the prefix inequality is an **equality**, namely
the cycle equation.  So the chain's only non-vacuous member carries no information
either. -/
theorem prefix_gap_at_L {n L g : Nat} (hgap : 2 ^ L = 3 ^ oddCount n L + g) :
    2 ^ L * affineC L n = 3 ^ oddCount n L * affineC L n + g * affineC L n := by
  rw [hgap, Nat.add_mul]

/-! ## The divergence-half filter, applied to the cycle criterion -/

/-- **`expStep` has no ledge.**  A window whose odd count is saturated — the defining
property of Round X's divergence-half witness `expStep` — has `2 ^ j < 3 ^ j` for
`j ≥ 1`, so the hypothesis `3 ^ a < 2 ^ L` of the cycle criterion is unsatisfiable.
Hence `G ∣ C ⟹ expStep contradiction` holds **vacuously**. -/
theorem expStep_no_ledge {x j : Nat} (hj : 0 < j) (hsat : oddCount x j = j) :
    ¬ (3 ^ oddCount x j < 2 ^ j) := by
  rw [hsat]
  have h : (2:Nat) ^ j < 3 ^ j := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- The contrapositive, in the form the criterion uses: a window admitting a positive
gap `2 ^ L − 3 ^ a` must have strictly fewer odd steps than steps.  So the cycle
criterion consumes `oddCount < j` — the even branch's contraction — in its hypothesis,
and Round X's soundness filter has nothing to say about it. -/
theorem oddCount_lt_of_ledge {x j : Nat} (hj : 0 < j) (hledge : 3 ^ oddCount x j < 2 ^ j) :
    oddCount x j < j := by
  rcases Nat.lt_or_ge (oddCount x j) j with h | h
  · exact h
  · exact absurd hledge
      (expStep_no_ledge hj (Nat.le_antisymm (AffineExact.oddCount_le_self x j) h))

/-! ## Axiom audit -/

#print axioms prefix_gap
#print axioms prefix_gap_of_heavy
#print axioms prefix_gap_at_L
#print axioms expStep_no_ledge
#print axioms oddCount_lt_of_ledge

end CoupledCycle
end Collatz
