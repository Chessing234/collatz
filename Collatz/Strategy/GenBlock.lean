import Collatz.Strategy.ShiftTrichotomy

/-!
# The `3n + c` family, and why `|c| = 1` is *not* a mechanism

`ShiftTrichotomy` proved the block law `F^a(2^a·w − c) = 3^a·w − c` for the three
hardcoded shifts `c = +1` (Collatz), `−1` (the mirror) and `0` (the divergent twin).
`gen_block` below is that statement with `c` left a **free odd parameter**, so the
trichotomy's three rows become three instances of one theorem.

## The question this file was written to answer, and the answer

The affine cycle equation for the family is, exactly,

`(2^L − 3^a) · x₀ = c · φ(s)`,

where `φ` is the ordinary Lagarias / Halbeisen–Hungerbühler accumulator
(`φ(∅)=0`, `φ(s0)=φ(s)`, `φ(s1)=3φ(s)+2^|s|`) applied to the cycle's own bit word —
**`φ`'s definition does not mention `c` at all.**  Verified on every cycle of `3n+c`
for odd `|c| ≤ 21` with small elements; no exception.

That made `|c| = 1` look like a mechanism: the gap must divide something
proportional to `c`, and `|c| = 1` is the tightest such divisibility.  `3n+5` and
`3n+7` do have nontrivial cycles; `3n+1` conjecturally does not.

**It is not a mechanism.  The scaling is trivial.**  Dividing a `3n+c` cycle by `c`
returns the *rational* `3n+1` cycle for the same word: the `c = 5` cycle
`(19, 31, 49, 76, 38)` divided by `5` is `(19/5, 31/5, 49/5, 76/5, 38/5)`, exactly
the rational fixed point that word already has under `3x+1`.  So an integer `3n+c`
cycle of shape `(L,a)` exists iff `gap | c·φ(s)` for some rotation, and small `|c|`
merely makes the same divisibility hardest to satisfy.  **This is an integrality
statement about one fixed combinatorial object, not different dynamics** — there is
no number-theoretic feature of `c = 1` beyond "smallest numerator is hardest to
divide".  Recorded here so the question is not reopened.

`gen_one_block_fixed_point_no_c_dependence` locates the same fact syntactically: at
the **one-block** level `c` cancels out of the fixed-point equation entirely,
leaving `3^a·w = 2^a·w`.  `c` is invisible until the multi-block accumulator — which
is exactly where the numerics found it.

## A correction

The prompt that produced this file asserted `hhMin` is a *lower* bound on the
accumulator.  It is an **upper** bound: `gap · x ≤ hhMin`, which is what makes the
criterion an exclusion.  `HalbeisenHungerbuhler.lean` states this, itself flagged as
a correction to an earlier misreading in this development.  The verdict above is
unaffected — the `c`-scaling of the bound is linear either way, and no violation of
`φ(s) ≤ hhMin(L,a,L)` was found at any `c`.

No new bound; `RealizableFrontier6809.length_ge_6809` is untouched.
-/

namespace Collatz
namespace GenBlock

/-- The accelerated `3n + c` map, `c` odd. -/
def genStep (c n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + c) / 2

/-- Its orbit. -/
def genOrbit (c : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => genOrbit c k (genStep c n)

/-- **The `c`-family block law.**  For every odd `c`, a maximal odd run of length
`a` starting at `2^a·w − c` ends at `3^a·w − c`, exactly as in `ShiftTrichotomy`'s
three rows — this is the same statement with `c` left as a free odd parameter
instead of specialized to `1`. The side condition `c ≤ 2^a * w` is exactly what
keeps the `Nat` subtraction faithful to the intended integer identity. -/
theorem gen_block (c : Nat) (hc : c % 2 = 1) :
    ∀ (a w : Nat), c ≤ 2 ^ a * w → genOrbit c a (2 ^ a * w - c) = 3 ^ a * w - c := by
  intro a
  induction a with
  | zero => intro w _; simp [genOrbit]
  | succ a ih =>
    intro w hle
    have hpow : 2 ^ (a + 1) * w = 2 * (2 ^ a * w) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hodd : ¬ ((2 ^ (a + 1) * w - c) % 2 = 0) := by omega
    have hstep : genStep c (2 ^ (a + 1) * w - c) = 2 ^ a * (3 * w) - c := by
      rw [genStep, if_neg hodd, hpow]
      have hx : 2 ^ a * (3 * w) = 3 * (2 ^ a * w) := Nat.mul_left_comm _ _ _
      omega
    have hle' : c ≤ 2 ^ a * (3 * w) := by
      have hx : 2 ^ a * (3 * w) = 3 * (2 ^ a * w) := Nat.mul_left_comm _ _ _
      omega
    rw [genOrbit, hstep, ih (3 * w) hle']
    have h3 : (3 : Nat) ^ (a + 1) * w = 3 ^ a * (3 * w) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    omega

/-- **The one-block fixed-point equation, `c`-scaled.**  A single-block cycle
`genOrbit c a (2^a·w − c) = 2^a·w − c` forces `w·(2^a − 3^a) = 0`... no — forces
`3^a·w − c = 2^a·w − c`, i.e. `w·(2^a − 3^a) = 0`, independent of `c` (`c` cancels).
So `c` cannot be recovered from the *one-block* fixed-point equation alone: this is
what forces the search to genuine multi-block cycles, where the accumulator
(not just `w`) carries the `c`-dependence. Recorded as a kill test: the naive
guess that `c` already shows up at one-block level is false. -/
theorem gen_one_block_fixed_point_no_c_dependence (c a w : Nat) (hc : c % 2 = 1)
    (hle : c ≤ 2 ^ a * w) (hle3 : c ≤ 3 ^ a * w)
    (hfix : genOrbit c a (2 ^ a * w - c) = 2 ^ a * w - c) :
    3 ^ a * w = 2 ^ a * w := by
  rw [gen_block c hc a w hle] at hfix
  omega

end GenBlock
end Collatz
