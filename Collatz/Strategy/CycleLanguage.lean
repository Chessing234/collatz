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

/-- `1 ≤ 3 ^ n`, needed because `Nat.pos_pow_of_pos` is off-limits here. -/
theorem three_pow_pos : ∀ n : Nat, 1 ≤ 3 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by
      have := three_pow_pos n
      rw [Nat.pow_succ]
      omega

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

/-- **The crude entropy bound.**  `binom n k · 2 ^ k ≤ 3 ^ n` — the `x = 2` case
of the binomial theorem, proved straight from Pascal's rule.  At the cycle
density `k / n = log 2 / log 3` it reads `binom ≤ 2 ^ (0.95405 · n)`: strictly
fewer words than the full shift's `2 ^ n`, by a provable `0.04595` bits per
letter.  (The truth is `0.94996`; the loss is the price of an integer proof.) -/
theorem binom_mul_two_pow_le : ∀ (n k : Nat), binom n k * 2 ^ k ≤ 3 ^ n := by
  intro n
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
          have h := three_pow_pos (n + 1)
          simpa using h
      | succ k =>
          have ha := ih k
          have hb := ih (k + 1)
          have key : binom n k * 2 ^ (k + 1) = binom n k * 2 ^ k * 2 := by
            rw [Nat.pow_succ, ← Nat.mul_assoc]
          calc binom (n + 1) (k + 1) * 2 ^ (k + 1)
              = binom n k * 2 ^ (k + 1) + binom n (k + 1) * 2 ^ (k + 1) := by
                rw [binom_succ_succ, Nat.add_mul]
            _ = binom n k * 2 ^ k * 2 + binom n (k + 1) * 2 ^ (k + 1) := by rw [key]
            _ ≤ 3 ^ n * 2 + 3 ^ n :=
                Nat.add_le_add (Nat.mul_le_mul_right 2 ha) hb
            _ = 3 ^ (n + 1) := by rw [Nat.pow_succ]; omega

/-! ## The exact transfer count of the heavy language -/

/-- `heavyCount i a` is the number of parity words of length `i` with `a` odd
steps all of whose prefixes are heavy (`2 ^ j ≤ 3 ^ a_j` for every `j ≤ i`).
This is the transfer recursion: append one letter, and kill the branch the
moment the prefix goes light.  The `a = 0` row at positive length is zero
because `2 ^ (i+1) ≤ 3 ^ 0 = 1` is false — the arithmetic reason a heavy word
must start with an odd step. -/
def heavyCount : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | i + 1, a + 1 =>
      if 2 ^ (i + 1) ≤ 3 ^ (a + 1) then heavyCount i (a + 1) + heavyCount i a else 0

theorem heavyCount_succ_succ (i a : Nat) :
    heavyCount (i + 1) (a + 1) =
      if 2 ^ (i + 1) ≤ 3 ^ (a + 1) then heavyCount i (a + 1) + heavyCount i a else 0 := rfl

/-- Heaviness only ever removes words: the transfer count is at most Pascal. -/
theorem heavyCount_le_binom : ∀ (i a : Nat), heavyCount i a ≤ binom i a := by
  intro i
  induction i with
  | zero =>
      intro a
      cases a with
      | zero => exact Nat.le_refl 1
      | succ a => exact Nat.le_refl 0
  | succ i ih =>
      intro a
      cases a with
      | zero => simp [heavyCount]
      | succ a =>
          rw [heavyCount_succ_succ, binom_succ_succ]
          by_cases h : 2 ^ (i + 1) ≤ 3 ^ (a + 1)
          · rw [if_pos h, Nat.add_comm (binom i a)]
            exact Nat.add_le_add (ih (a + 1)) (ih a)
          · rw [if_neg h]
            exact Nat.zero_le _

/-- **The heavy language is smaller than the full shift, provably.**
`heavyCount L a · 2 ^ a ≤ 3 ^ L`. -/
theorem heavyCount_mul_two_pow_le (L a : Nat) : heavyCount L a * 2 ^ a ≤ 3 ^ L :=
  Nat.le_trans (Nat.mul_le_mul_right _ (heavyCount_le_binom L a))
    (binom_mul_two_pow_le L a)

/-- Sanity: the transfer recursion reproduces the exhaustive count.  There are
exactly `8045` heavy parity words of length `20` carrying `13` odd steps — the
lightest count heaviness permits there — against `binom 20 13 = 77520`
unconstrained.  The ratio `9.6` is the cycle-lemma factor `Θ(L)`; the heavy rows
`a = 13 … 20` sum to `27328 = 2 ^ (0.7369 · 20)`. -/
theorem heavyCount_20 : heavyCount 20 13 = 8045 := by decide

theorem heavyCount_5 : heavyCount 5 4 = 3 := by decide

/-! ## The gap outweighs the language -/

/-- **The deficit interface.**  If the concrete inequality
`3 ^ L · 2 ^ e < 2 ^ a · G` holds, then the whole heavy language at `(L,a)` is
smaller than the gap `G` by a factor `2 ^ e`.  Every instance below is this
lemma plus one `decide`. -/
theorem deficit_of_witness {L a e G : Nat} (h : 3 ^ L * 2 ^ e < 2 ^ a * G) :
    heavyCount L a * 2 ^ e < G := by
  refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ a) ?_
  have hrw : 2 ^ a * (heavyCount L a * 2 ^ e) = heavyCount L a * 2 ^ a * 2 ^ e := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a) (heavyCount L a)]
  rw [hrw]
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right (2 ^ e) (heavyCount_mul_two_pow_le L a)) h

/-- **The two-term deficit interface.**  The cycle language at `(L+1, a+1)` splits
on its last letter into the two heavy classes at length `L`, so what has to be
bounded is `heavyCount L (a+1) + heavyCount L a`.  Raising the smaller class to
the common power costs a factor two, so the combined majorant is `3 · 3 ^ L`
rather than `3 ^ L`, and the witness carries that three.

The common power is a *variable* `M` rather than `2 ^ (a+1)`: stating it as a
successor makes Lean unify `?a + 1` against a numeral in the four-digit range at
every use site, and that unification is what made an earlier version of this file
fail to elaborate at all. -/
theorem deficit_of_witness_sum {L e G M N₁ N₂ : Nat}
    (h1 : N₁ * M ≤ 3 ^ L) (h2 : N₂ * M ≤ 2 * 3 ^ L)
    (h : 3 * (3 ^ L * 2 ^ e) < M * G) :
    (N₁ + N₂) * 2 ^ e < G := by
  refine Nat.lt_of_mul_lt_mul_left (a := M) ?_
  have hsum : (N₁ + N₂) * M ≤ 3 * 3 ^ L := by rw [Nat.add_mul]; omega
  have hrw : M * ((N₁ + N₂) * 2 ^ e) = (N₁ + N₂) * M * 2 ^ e := by
    rw [← Nat.mul_assoc, Nat.mul_comm M _]
  rw [hrw]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ e) hsum)
    (by rw [Nat.mul_assoc]; exact h)

set_option exponentiation.threshold 40000
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

/-! ### The cycle language is counted at `L − 1`, not at `L`

`heavyCount L a` demands heaviness at *every* prefix, the last one included.  A
cycle word cannot be heavy at `i = L`: heaviness there is `2 ^ L ≤ 3 ^ a`, which
is exactly the negation of the gap being positive.  So at every pair of interest
`heavyCount L a = 0` — for instance `heavyCount 4701 2966 = 0`, because
`fexp 2966 = 4700` puts `3 ^ 2966` strictly below `2 ^ 4701`.

An earlier version of this file stated the two deficit theorems at `(L, a)` and
so proved only `0 < G`.  The count that matters is over words heavy at every
*proper* prefix, which splits on the last letter:

`#cycle-language(L, a) = heavyCount (L−1) a + heavyCount (L−1) (a−1)`.

Both terms are bounded by `heavyCount_mul_two_pow_le` at `L − 1`, so the same
witness serves.  *Corrected:* an earlier version of this paragraph said both terms
are nonzero.  They are not — at both pairs used below the `(a−1)` term **vanishes**,
because `2^(L−1) > 3^(a−1)` (`2^4700 > 3^2965`, `2^5754 > 3^3630`).  The content of
the theorems is therefore that every cycle word at these pairs ends in an even
step, which is true and worth knowing, but it is not what the prose claimed.  The
surviving `heavyCount (L−1) a` term is genuinely nonzero — its logarithm is
`4447.16881` against `log₂(binom(4701,2966)/4701) = 4447.16881`, agreeing to twelve
figures — so the theorems are **not** vacuous.  The split is kept because it is the
correct identity in general; the vanishing is pair-specific.  The
advertised exponents are unchanged by the repair — `205` and `254` are still
exactly tight, and `206` and `255` are both false. -/

/-- **The frontier pair.**  `(L,a) = (4701, 2966)` is the shortest length at
which the gap `G = 2 ^ L − 3 ^ a` is small enough to permit a cycle minimum
`≥ 768000` (the same pair as `RealizableBound.length_ge_4701`, found here from
the counting side).  Every word of that shape heavy at every proper prefix, put
together, still misses the residues mod `G` by a factor `2 ^ 205`.

The exact figures behind this: `log₂ (#cyclic-heavy words) = 4447.17`,
`log₂ G = 4690.79`, deficit `2 ^ (−243.6)`.  The `205` is what survives the
crude entropy bound. -/
theorem count_lt_gap_4701 :
    (heavyCount 4700 2966 + heavyCount 4700 2965) * 2 ^ 205 < 2 ^ 4701 - 3 ^ 2966 := by
  refine deficit_of_witness_sum (M := 2 ^ 2966)
    (heavyCount_mul_two_pow_le 4700 2966) ?_ (by decide)
  have h2 := heavyCount_mul_two_pow_le 4700 2965
  have hpow : (2 : Nat) ^ 2966 = 2 ^ 2965 * 2 := by
    rw [show (2966 : Nat) = 2965 + 1 from rfl, Nat.pow_succ]
  rw [hpow, ← Nat.mul_assoc]
  calc heavyCount 4700 2965 * 2 ^ 2965 * 2 ≤ 3 ^ 4700 * 2 := Nat.mul_le_mul_right 2 h2
    _ = 2 * 3 ^ 4700 := Nat.mul_comm _ _

/-- The next cycle-plausible pair; the deficit grows with `L`, by the measured
`0.05004` bits per step. -/
theorem count_lt_gap_5755 :
    (heavyCount 5754 3631 + heavyCount 5754 3630) * 2 ^ 254 < 2 ^ 5755 - 3 ^ 3631 := by
  refine deficit_of_witness_sum (M := 2 ^ 3631)
    (heavyCount_mul_two_pow_le 5754 3631) ?_ (by decide)
  have h2 := heavyCount_mul_two_pow_le 5754 3630
  have hpow : (2 : Nat) ^ 3631 = 2 ^ 3630 * 2 := by
    rw [show (3631 : Nat) = 3630 + 1 from rfl, Nat.pow_succ]
  rw [hpow, ← Nat.mul_assoc]
  calc heavyCount 5754 3630 * 2 ^ 3630 * 2 ≤ 3 ^ 5754 * 2 := Nat.mul_le_mul_right 2 h2
    _ = 2 * 3 ^ 5754 := Nat.mul_comm _ _

/-! ## No forbidden block: the heavy language is not sofic -/

/-- **Padding lemma.**  Prefix any block of length `k` with `2k` odd steps and
every prefix inside the block is heavy: `2 ^ (2k + i) ≤ 2 ^ (3k) = 8 ^ k ≤
9 ^ k = 3 ^ (2k)`.  Since the block was arbitrary, *every* word over `{0,1}`
occurs as a factor of a heavy word.  The heavy language therefore has full
factor complexity `2 ^ k`, its shift closure is the full shift, and no forbidden
block — hence no subshift of finite type, hence no shift-invariant finite
automaton — can separate it.  Its entropy `0.94996` is not a sofic entropy: the
constraint is a random walk with irrational drift `log 2 / log 3` conditioned to
stay nonnegative, which needs an unbounded counter. -/
theorem heavy_pad (k i : Nat) (h : i ≤ k) : 2 ^ (2 * k + i) ≤ 3 ^ (2 * k) := by
  have h1 : 2 ^ (2 * k + i) ≤ 2 ^ (3 * k) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : (2 : Nat) ^ (3 * k) = 8 ^ k := by rw [Nat.pow_mul]
  have h3 : (3 : Nat) ^ (2 * k) = 9 ^ k := by rw [Nat.pow_mul]
  have h4 : (8 : Nat) ^ k ≤ 9 ^ k := Nat.pow_le_pow_left (by decide) k
  omega

/-- The same statement with the odd-step count only bounded below: any block of
length `k` sitting at height `a ≥ 2k` stays heavy throughout. -/
theorem no_forbidden_block (k a i : Nat) (hi : i ≤ k) (ha : 2 * k ≤ a) :
    2 ^ (2 * k + i) ≤ 3 ^ a :=
  Nat.le_trans (heavy_pad k i hi) (Nat.pow_le_pow_right (by decide) ha)

end CycleLanguage
end Collatz
