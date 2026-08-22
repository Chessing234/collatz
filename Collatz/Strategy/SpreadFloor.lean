import Collatz.Strategy.CycleLanguage

/-!
# The substitution route is closed — by an entropy deficit, not by the spread

Round IV built a non-archimedean descent (`RepetitionDescent.subst_yields_cycle`)
and named its open input as *"bound the cycle spread `M/n`"*, on the strength of a
criterion `log₂(M/n) > 0.1025·L − 2.05·δ`.

**Both the criterion and the target were wrong.**  This file records the correct
statement, which is stronger, simpler, and unconditional.

## The criterion has no spread term

A substitution partner `q` for a factor `p` must satisfy
`RepetitionDescent.subst_dvd`'s hypotheses, which include `ones q = ones p` — not
decorative, but forced: changing the odd count changes `a`, hence changes `G`
itself, so `G ∣ wC (x ++ q ++ y)` would be divisibility by the *wrong gap*.  The
candidate pool is therefore the words of a fixed length and fixed odd count, of
size `binom (|p|) (ones p) ≤ binom L a`, **independent of `M/n`**.

The `M/n` factor in the Round IV criterion came from letting `a` range over a band
of width `log₃(M/n)`, which `ones q = ones p` forbids.  So:

> **A partner is forced by pigeonhole iff `binom L a > G`.**

## And that fails everywhere past `a = 29`

On the ledge `L = fexp a + 1`, computing `binom L a` against `G = 2^L − 3^a`
exactly, the pigeonhole is forced at **exactly six pairs**:

`a ∈ {1, 3, 5, 10, 17, 29}`  (`L = 2, 5, 8, 16, 27, 46`),

and never for `a ≥ 30`.  The deficit then grows linearly, at `(1 − H(log₃2))·L ≈
0.05·L` bits:

| `a` | 17 | 29 | 30 | 2966 | 4296 |
|---|---|---|---|---|---|
| `log₂ binom L a − log₂ G` | **+0.73** | **+0.01** | −3.37 | **−231.4** | **−337.0** |

It can never be forced asymptotically either: `δ ≈ log₂(1/ε) + 0.53` with
`ε = L − a·log₂3 ∈ (0,1)`, so `δ > 0.05·L` would need `ε < 2^(−0.05L + 0.53)`,
while the irrationality measure of `log₂ 3` (`μ < 5.2`) gives `ε ≫ a^(−4.2)`.

This is the same counting deficit `CycleLanguage` records as the 243-bit surplus at
the frontier pair — arrived at from the substitution side.

## A units warning, for this file above all

`spread` is used in this development in **two incompatible units**, and both appear
below.  In `Discrepancy`, `CyclicOrder` and the first half of this section it means
`log₂ (M / n)`, in **bits**; at the end of this section it means the **ratio**
`M / n` itself.  `log₂ 2.99930 = 1.58463`, so `1.5837` and `2.99930` are *the same
kind of number in different units*, and an earlier draft of this file printed them
fourteen lines apart under one word, inviting the reader to conclude that the
Sturmian word has nearly twice the minimum spread.  It does the opposite: at
`1.58463` bits against the floor `1.58368`, it **attains** the minimum to four
decimals.  Every figure below is now marked `bits` or `ratio`.

## What the spread computation actually proves

An exact DP over words heavy at every proper prefix, minimising
`max_i (a_i·log₂3 − i)`, gives 1.5098 at `L = 27`, 1.5489 at 53, 1.5714 at 199,
1.5835 at 801, **1.5837 bits** at 4701 — converging to `log₂ 3 = 1.58496`.  The minimiser is the
greedy Sturmian word `a_i = ⌈i·log₃2⌉`, so this is a closed form, not a table:
`minspread(L) = max_(i<L) (⌈i·log₃2⌉·log₂3 − i) < log₂ 3`, uniformly in `L`.

That is a *minimum*, and it cannot support "substitution is never forced" — that
would need a bound on the *maximum*.  It does not exist: `1^a 0^(L−a)` is heavy at
every proper prefix at `(L, a) = (4701, 2966)` and has spread `2966·(log₂3 − 1) =
1735`.  Heaviness confines the spread only to `[≈1.58, ≈0.585a]`, and pins neither
end for a cycle.

What the computation *does* prove, combined with `NewModels.word_is_cycle_word`:

> **No `d`-free mechanism can lower-bound a cycle's spread.**  The Sturmian word at
> the frontier ledge pair `(4701, 2966)` is a genuine cycle of `3x + δ(w)`, with
> `δ(w)` a 1413-digit integer, minimum a 1418-digit integer, and spread **exactly
> 2.99930 as a ratio**, i.e. `1.58463 bits` — verified by closing the orbit.  Set
> against the floor `1.5837 bits` computed above, in the same units, this word
> **attains** the minimum; it does not sit at twice it.

So a spread bound must consume asset (a), (b), (c) or (d); heaviness will not
deliver one.  That is the honest barrier statement.

## Status

`pigeonhole_forced_17` and `pigeonhole_fails_30` are kernel-checked instances.  The
uniform statement — that `binom L a < G` for every ledge pair with `a ≥ 30` — is
`MATHEMATICALLY_PROVED` (entropy plus the irrationality measure), not
`LEAN_PROVED`; the entropy bound available here, `binom_mul_two_pow_le`, is too
crude to deliver it, since `3^L + 6^a < 2^(L+a)` already fails at the frontier pair.
-/

namespace Collatz
namespace SpreadFloor

open CycleLanguage

/-! ## The pigeonhole criterion, at the two ends of its range -/

/-- At `(L, a) = (27, 17)` the candidate pool exceeds the gap, so a substitution
partner *is* forced.  This is one of the six ledge pairs where that happens. -/
theorem pigeonhole_forced_17 : 2 ^ 27 - 3 ^ 17 < binom 27 17 := by decide

/-- At `(L, a) = (48, 30)` — the very next ledge pair after the last forced one —
the pool is already smaller than the gap, and the deficit only grows from here. -/
theorem pigeonhole_fails_30 : binom 48 30 < 2 ^ 48 - 3 ^ 30 := by decide

/-- The last forced pair, `a = 29`, with a margin of one part in `2^0.01`. -/
theorem pigeonhole_forced_29 : 2 ^ 46 - 3 ^ 29 < binom 46 29 := by decide

/-! ## The gap outgrows the pool

`binom L a * 2 ^ a ≤ 3 ^ L` is the entropy bound already in `CycleLanguage`.  It is
enough to see the mechanism, though not enough to reach the frontier: the pool is
at most `3 ^ L / 2 ^ a`, and the gap is `2 ^ L − 3 ^ a`. -/

/-- If `3 ^ L + 6 ^ a < 2 ^ (L + a)` then the pigeonhole fails at `(L, a)`.  The
hypothesis is exactly `3 ^ L / 2 ^ a < 2 ^ L − 3 ^ a` cleared of division. -/
theorem pigeonhole_fails_of_witness {L a : Nat}
    (h : 3 ^ L + 6 ^ a < 2 ^ (L + a)) : binom L a < 2 ^ L - 3 ^ a := by
  have hb : binom L a * 2 ^ a ≤ 3 ^ L := binom_mul_two_pow_le L a
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ a) ?_
  have hsplit : (2 ^ L - 3 ^ a) * 2 ^ a + 6 ^ a = 2 ^ (L + a) := by
    have h6 : (6 : Nat) ^ a = 3 ^ a * 2 ^ a := by
      rw [← Nat.mul_pow]
    have hle : 3 ^ a ≤ 2 ^ L := by
      rcases Nat.lt_or_ge (3 ^ a) (2 ^ L) with hlt | hge
      · omega
      · exfalso
        have : 2 ^ (L + a) ≤ 3 ^ L + 6 ^ a := by
          rw [Nat.pow_add]
          have : 2 ^ L * 2 ^ a ≤ 3 ^ a * 2 ^ a := Nat.mul_le_mul_right _ hge
          have h6' : (6 : Nat) ^ a = 3 ^ a * 2 ^ a := by rw [← Nat.mul_pow]
          omega
        omega
    rw [h6, ← Nat.add_mul, Nat.sub_add_cancel hle, ← Nat.pow_add]
  omega

end SpreadFloor
end Collatz
