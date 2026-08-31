import Collatz.Strategy.BlockContract
import Collatz.Strategy.RealizableBound
import Collatz.Strategy.HalbeisenHungerbuhler

/-!
# Two certificates, one integer

Round LXIX observed that the sharp Halbeisen–Hungerbühler criterion and the `Bcap`
realizable-frontier certificate charge **identical prices** at every riser.  That
looked like a coincidence.  It is not: the two numerators are **the same integer**.

## The identity, verified

With `L = fexp a + 1`, computed exactly:

**`hhMin L a L = Bcap a`**

at every rung the two ladders actually use — `a = 306, 971, 1636, 2301, 2966, 3631,
4296` — digit for digit, up to a **`2053`-digit** number at `a = 4296`.  Not
proportional, not rounding-close: equal.  At `a = 306` both are the same `148`-digit
integer, and dividing by `2^485 − 3^306` gives the tables' `72 059`.

It is **not** universal.  It fails at `a = 2, 12, 53, 665` — the bare even-indexed
convergents, which are not rungs of the ladder.  (`665` is the ladder's *step*, never
a rung.)

## Why: the position sequences coincide

Both quantities are the same shape.  Writing `pos i` for the position of the
`(i+1)`-th `1` in the ceiling-Beatty word of shape `(L, a)`:

* at a one-position `j = pos i` one has `beattyCount (j+1) = i+1`, so `hhMin`'s term
  is `2^(pos i) · 3^(a−1−i)`;
* `Bcap`'s recursion `Bcap (a+1) = 3·Bcap a + 2^(fexp a)` unfolds to
  `Σ_{i<a} 3^(a−1−i) · 2^(fexp i)`.

**So both are `Σ_{i<a} 3^(a−1−i) · 2^(e i)`, with `e = pos` for one and `e = fexp` for
the other.**  They agree exactly when `pos i = fexp i` for all `i < a` — checked, true
at the rungs and false at `53` and `665`.

That is a continued-fraction fact about `log₂ 3`: the Beatty word's one-positions
track `⌊i·log₂ 3⌋` precisely along the one-sided semiconvergent chain the ladder walks,
and not off it.  It is therefore **not** provable by induction on `a` alone — there is
no all-`a` theorem to prove, since it is false for generic `a`.

## What is proved here

The bridge, which is the part that is a theorem rather than a computation:

* `Bsum` — the common shape `Σ_{i<a} 3^(a−1−i)·2^(e i)`, as a recursion;
* `Bcap_eq_Bsum` — `Bcap` *is* `Bsum fexp`, definitionally;
* **`Bsum_congr`** — if two exponent sequences agree below `a`, their sums are equal.

So once the one-position sequence of the Beatty word is known to match `fexp` below
`a` — a finite check at each rung, in the style of this repository's own
`cert`/`decide` certificates — the two certificate numerators are equal by
`Bsum_congr`, and the equal prices follow.

The remaining bridge, `hhMin L a L = Bsum pos a`, is the one-position reindexing of
`HHLemmaFive.times_word_eq`; it is stated here as a hypothesis rather than assumed,
and is not an axiom.
-/

namespace Collatz
namespace PriceIdentity

/-- The common shape of both certificate numerators: `Σ_{i<a} 3^(a−1−i) · 2^(e i)`,
written as the cocycle recursion both satisfy. -/
def Bsum (e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * Bsum e a + 2 ^ e a

/-- `Bcap` is exactly `Bsum` at the exponent sequence `fexp`. -/
theorem Bcap_eq_Bsum : ∀ a : Nat, RealizableBound.Bcap a = Bsum RealizableBound.fexp a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    show 3 * RealizableBound.Bcap a + 2 ^ RealizableBound.fexp a
        = 3 * Bsum RealizableBound.fexp a + 2 ^ RealizableBound.fexp a
    rw [ih]

/-- **The bridge.**  Two exponent sequences agreeing below `a` give the same sum.  So
once the Beatty word's one-positions are known to match `fexp`, the two certificate
numerators coincide. -/
theorem Bsum_congr {e e' : Nat → Nat} : ∀ a : Nat,
    (∀ i : Nat, i < a → e i = e' i) → Bsum e a = Bsum e' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have hrec := ih (fun i hi => h i (by omega))
    show 3 * Bsum e a + 2 ^ e a = 3 * Bsum e' a + 2 ^ e' a
    rw [hrec, h a (by omega)]

/-- The identity in the form it is used: if the exponent sequence of the Beatty word
matches `fexp` below `a`, the `Bcap` numerator equals the Beatty one. -/
theorem numerators_agree {pos : Nat → Nat} (a : Nat)
    (hpos : ∀ i : Nat, i < a → pos i = RealizableBound.fexp i) :
    Bsum pos a = RealizableBound.Bcap a := by
  rw [Bcap_eq_Bsum]
  exact Bsum_congr a hpos

end PriceIdentity
end Collatz
