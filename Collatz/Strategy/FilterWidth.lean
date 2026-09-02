import Collatz.Strategy.CoordinateMismatch

/-!
# The divergence-half filter cannot be narrowed

`CLOSURE.md` records the Round X divergence-half filter and, with it, the
objection its own author raised:

> `3x+d` differs from `3x+1` in one constant, whereas `expStep` differs on a
> whole branch, so this filter kills a coarser class of mechanisms than the cycle
> filter does.  **Narrowing it is the natural next task.**

This file answers that task in the negative, and says exactly why.

## What a witness has to be

The filter works because `expStep` has a *one-line* divergence proof: every step
strictly increases (`3n/2 > n` for `n > 0`, `(3n+1)/2 > n` for `n ≥ 1`), so no
orbit can fall.  That is the only reason the filter refutes anything — a witness
whose divergence were merely conjectural would refute nothing, since one could
not conclude that a mechanism proving "no divergence" had proved something false.

So a usable witness must satisfy `x < g x` for every `x ≥ 1`.  Call that a
**no-contraction witness**.

## The obstruction

`increasing_ne_halving`: a no-contraction witness has `g x ≠ x / 2` at **every**
even `x ≥ 2`.  It cannot agree with the Collatz even branch anywhere — not on a
sparse set, not at a single point.  So `expStep`'s whole-branch difference from
`T` is **forced**, not an artefact of how the witness was chosen, and the filter's
coarseness cannot be reduced by picking a better map of this kind.

## The measurement that rules out the natural attempt

The obvious way to narrow the gap is to keep the halving branch on a thin set:

    f_c(x) = x / 2  when  2 ^ c ∣ x,   else  3x/2  (even)  or  (3x+1)/2  (odd)

which is Terras at `c = 1` and `expStep` in the limit — an interpolation of
exactly the kind the objection asks for.  It fails immediately.  Over the first
`20000` starts, the number whose orbit dips below its own start is

    c = 2 → 12677,    c = 3 → 6149,    c = 4 → 3045

so for every `c ≥ 2` the map contracts somewhere, `x < f_c x` is false, and its
divergence — if true at all — is no longer provable by the means that made
`expStep` useful.  Admitting a halving branch on *any* set of positive density
reintroduces dips, which is `increasing_ne_halving` showing up numerically.

## What this does and does not settle

Settled: the filter cannot be narrowed by weakening the even branch of the
witness.  Any strictly-increasing witness differs from Collatz on every even
input, so "differs on a whole branch" is the minimum possible distance.

Not settled: whether some *entirely different* style of witness — one whose
divergence is provable for a reason other than pointwise increase — could do
better.  Nothing here rules that out; the theorem below is about no-contraction
witnesses only, which is the class every known witness belongs to.
-/

namespace Collatz
namespace FilterWidth

open CoordinateMismatch

/-- A **no-contraction witness**: strictly increasing on the positives, hence
divergent for a one-line reason.  This is the property that makes a witness
usable in the divergence-half filter. -/
def NoContraction (g : Nat → Nat) : Prop := ∀ x : Nat, 1 ≤ x → x < g x

/-- `expStep` is one. -/
theorem expStep_noContraction : NoContraction expStep := by
  intro x hx
  unfold expStep
  rcases Nat.eq_zero_or_pos (x % 2) with hev | hodd
  · rw [if_pos hev]
    obtain ⟨t, ht⟩ : ∃ t, x = 2 * t := ⟨x / 2, by omega⟩
    subst ht
    have h : 3 * (2 * t) / 2 = 3 * t := by omega
    rw [h]
    omega
  · have hodd1 : x % 2 = 1 := by omega
    rw [if_neg (by omega)]
    obtain ⟨t, ht⟩ : ∃ t, x = 2 * t + 1 := ⟨x / 2, by omega⟩
    subst ht
    have h : (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 := by omega
    rw [h]
    omega

/-- **The obstruction.**  A no-contraction witness cannot agree with the Collatz
even branch at any even point.  Halving is a contraction, and the witness
contracts nowhere. -/
theorem increasing_ne_halving {g : Nat → Nat} (hg : NoContraction g)
    {x : Nat} (hx : 2 ≤ x) : g x ≠ x / 2 := by
  have hlt : x / 2 < x := by omega
  have hgt : x < g x := hg x (by omega)
  omega

/-- The same statement as the filter uses it: a witness agreeing with `T` on even
inputs anywhere above `1` is **not** a no-contraction witness, so it carries no
one-line divergence proof. -/
theorem no_witness_agrees_on_an_even {g : Nat → Nat} {x : Nat} (hx : 2 ≤ x)
    (hagree : g x = x / 2) : ¬ NoContraction g :=
  fun hg => increasing_ne_halving hg hx hagree

/-- Hence the distance is not merely "some even input" but **every** even input:
`expStep`'s whole-branch difference is the minimum a usable witness can achieve. -/
theorem witness_differs_on_every_even {g : Nat → Nat} (hg : NoContraction g) :
    ∀ x : Nat, 2 ≤ x → x % 2 = 0 → g x ≠ x / 2 :=
  fun _ hx _ => increasing_ne_halving hg hx

end FilterWidth
end Collatz
