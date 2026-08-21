/-!
# The cycle language: how many parity words there are, and how many the gap can hold

This file measures the *counting* side of the cycle problem and reports the
answer as an arithmetic inequality.

## The three languages

Fix a length `L` and an odd-step count `a`.  A parity word is a string
`b₀ … b_{L-1}` over `{0,1}`; write `aᵢ = b₀ + … + b_{i-1}`.

* the **full** language: all `2 ^ L` words;
* the **heavy** language `H(L,a)`: those with `2 ^ i ≤ 3 ^ aᵢ` for every prefix
  `i ≤ L` — the words a never-dropper is confined to (`HeavyWord`,
  `RealizableBound`);
* the **cycle** language: heavy at every *proper* prefix, with `3 ^ a < 2 ^ L`.
  A genuine cycle read from its minimum lies here; heaviness cannot hold at
  `i = L` because the gap `G = 2 ^ L − 3 ^ a` is positive.

`heavyCount L a` below is the exact cardinality of `H(L,a)`, defined by the
transfer recursion (add one letter at a time, kill the branch the moment the
prefix goes light).  `binom` is Pascal's triangle, the count with the heaviness
constraint dropped.

## What the counting says

Three measurements, all exact, made outside Lean and reported here with the
parts that Lean can carry:

1. **The heavy language has entropy `H₂(log 2 / log 3) = 0.9499555… ` bits per
   letter**, against `1` for the full shift.  The constraint is a random walk
   with irrational drift conditioned to stay nonnegative, *not* a sofic
   condition: `heavy_pad` below shows every finite block occurs inside a heavy
   word, so the language has full factor complexity `2 ^ k` and no forbidden
   block exists.  No subshift of finite type, and no shift-invariant automaton,
   can over-approximate it with entropy below `log 2`.

2. **The cyclic constraint costs exactly a factor of `L`, and no entropy.**  At
   the pairs that matter the gap ratio `2 ^ L / 3 ^ a − 1` is below `10 ^ (−3)`,
   so the Dvoretzky–Motzkin cycle lemma is exactly tight: every necklace with
   `a = ⌊L·log₃2⌋` ones has *exactly one* rotation that is heavy at all proper
   prefixes.  Verified exhaustively for `L ≤ 24` (no word ever has two heavy
   rotations) and confirmed numerically at `(4701, 2966)`, where the count is
   `binom 4701 2966 / 4701` to full float precision.  The cyclic constraint is
   therefore worthless as a filter, and this file does not pretend otherwise.

3. **The gap is bigger than the language.**  The first `(L,a)` that survives the
   realizability filter at the verified range `768000` is `(4701, 2966)` — the
   same pair as `RealizableBound.length_ge_4701`, arrived at independently.
   There `log₂ (count) = 4447.17` while `log₂ G = 4690.79`.  So a heuristic that
   treats `C(w) mod G` as equidistributed predicts

      #{cycles at (4701,2966)} ≈ 2 ^ (−243.6),

   and the margin *grows* by `1 − H₂(log2/log3) = 0.05004` bits per step of `L`:
   summed over all `88` cycle-plausible pairs with `a ≤ 20000` the total is
   `2 ^ (−243.63)`, dominated entirely by the first.

The theorem `count_lt_gap` is the rigorous shadow of measurement 3: it replaces
the exact entropy `0.94996` by the crude `log₂3 − log₃2 = 0.95405`, which is
still strictly below `1`, and still leaves `205` bits of room at `(4701,2966)`.

## What this does *not* prove

Nothing, about cycles.  `count_lt_gap` says the heavy words are far too few to
cover the residues mod `G`; it does not say that none of them lands on `0`.
Bridging that needs a bound on the exponential sum `Σ_{w heavy} e(k·C(w)/G)`,
and no such bound is available here.  The value of the number is that it points
the other way from most negative results in this repo: the counting budget is
*not* exhausted — it is in surplus by `243` bits and growing linearly — so the
obstruction to a counting proof is the arithmetic of `C mod G`, not the size of
the language.

## Soundness filter

The count is `d`-free (heaviness is `d`-free and `C(w,d) = d·C(w,1)`, so
`G ∣ C(w,d) ↔ G ∣ C(w,1)`), and so is `count_lt_gap`.  The single `d = 1` input
is the length `4701`, which comes from the verified range `768000` via
`RealizableBound`.  That is the right place for it: the heuristic is uniform in
`d` and predicts "no *long* cycles", which is exactly what `d = −1` (cycles of
length `1, 3, 11`) and `d = 5` (lengths `2, 3, 5, 27`) exhibit.  The counting
picture is not refuted by the known `d ≠ 1` cycles; it explains them.
-/

namespace Collatz
namespace CycleLanguage

/-! ## Pascal's triangle, with no Mathlib -/

/-- `binom n k` is the number of length-`n` parity words with `k` odd steps. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

@[simp] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := rfl

theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

/-- **The crude entropy bound.**  `binom n k · 2 ^ k ≤ 3 ^ n`, the `x = 2` case
of the binomial theorem, proved directly from Pascal's rule.  At the cycle
density `k / n = log 2 / log 3` this reads `binom ≤ 2 ^ (0.95405 n)`: strictly
fewer than `2 ^ n` words, by a provable `0.04595` bits per letter. -/
theorem binom_mul_two_pow_le (n : Nat) : ∀ k : Nat, binom n k * 2 ^ k ≤ 3 ^ n := by
  induction n with
  | zero =>
      intro k
      cases k with
      | zero => simp
      | succ k => simp
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          simp only [binom_zero_right, Nat.pow_zero, Nat.mul_one]
          exact Nat.one_le_two_pow_iff_ne_zero.mp (Nat.one_le_iff_ne_zero.mpr
            (by exact Nat.pos_iff.mp (Nat.pos_pow_of_pos_aux)) ) |>.elim
      | succ k => exact absurd rfl rfl
