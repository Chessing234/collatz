import Collatz.Core.Sum
import Collatz.Strategy.CycleLanguage

/-!
# Forward heaviness and backward density are one generating function

Round VI recorded a numerical coincidence: the counting exponent of *bounded
reverse paths* (`BackwardRange` §4) is `1 − H(log₃ 2) = 0.0500445`, the same
number as the *forward heavy-word deficit* (`CycleLanguage`).  This file
establishes that it is not a coincidence, identifies the single object both
sides are reading, and then shows — this is the load-bearing half — that the
object is **`(L, a)` and nothing else**, so the duality is real and vacuous.

## 1. The exact sense in which the two counts are one

Fix a length `L`.  Let `hᵃ := heavyCount L a` be the number of parity words of
length `L` with `a` odd steps, heavy at every prefix.  Define one polynomial

  `F_L(x, y) = Σ_{a ≤ L} hᵃ · xᵃ · y^(L−a)`   (`gf L (heavyCount L) x y` below).

Then, *exactly*, with no asymptotics:

* **forward count** `= F_L(1, 1) = Σ_a hᵃ` — the number of heavy words;
* **reverse weight** `= F_L(1, 3) / 3^L = Σ_a hᵃ · 3^(−a)` — the total
  endpoint-density of those words in the reverse tree, because by
  `BackwardRange.endpoint_class` the endpoints realising a fixed word of `a` ones
  form **one residue class mod `3 ^ a`**, of density `3^(−a)`.

Two evaluations of one polynomial.  That is the whole identity; there is no
bijection, and none is possible, because the two sides are not equinumerous —
they are the *same coefficient vector paired with two different weightings*.

## 2. Why the exponents agree: `3 ^ (log₃ 2) = 2`, and nothing else

The forward density weight and the reverse density weight are

* forward (Terras): the words of length `L` cut out one class mod `2 ^ L`,
  density `2^(−L)`, the same for every word;
* reverse (`endpoint_class`): a word with `a` ones cuts out one class mod
  `3 ^ a`, density `3^(−a)`, depending on the word only through `a`.

**Heaviness is precisely the comparison of these two densities.**  `w` is heavy
at its last prefix iff `2 ^ L ≤ 3 ^ a`, i.e. iff `3^(−a) ≤ 2^(−L)`, i.e. iff the
reverse class is at least as sparse as the forward class (`heavy_iff_rev_le_fwd`).
So the heavy language is *defined* by the inequality that equates the two
weightings, and at the binding density `a = ⌈L·log₃2⌉` the two weights agree to
within a factor `3` (`term_sandwich`, exact, `Nat`-only).  This is why the
exponents must differ by exactly `1` bit per letter:

  forward exponent `= H(log₃2) = 0.9499555`
  reverse exponent `= H(log₃2) − log₃2 · log₂3 = H(log₃2) − 1 = −0.0500445`

and `log₃2 · log₂3 = 1` is the *only* arithmetic input.  Measured (exact rational
arithmetic on the transfer recursion, `L ≤ 4701`): `log₂(forward)/L` runs
`0.9011, 0.9212, 0.9334, 0.9405, 0.9446, 0.9468`, and `log₂(reverse)/L` runs
`−0.1141, −0.0870, −0.0709, −0.0616, −0.0566, −0.0539` at `L = 160, 320, 640,
1280, 2560, 4701`.  The exact relation these obey is *additive, with a bounded
error*: `log₂(reverse) = log₂(forward) − L + O(1)`, the `O(1)` being
`log₂(reverse/(forward·2^(−L)))`, measured to lie in `[−3.41, −2.44]` for every
`L` from `40` to `4701` — a hundred-fold range with no drift.  Dividing by `L`
gives `reverse exponent = forward exponent − 1` in the limit, which is the
statement above.  `reverse_le_forward` below is the upper half of
that sandwich, proved.

## 3. The operator, and the Round III objection

Both counts are governed by *one* transfer operator, and it is `1 × 1`, not
`2 × 2`.  The word monoid is free (Round III), so on the full shift the transfer
operator with a per-letter weight `(y for `0`, x for `1`)` is the rank-one matrix
`[[y, x], [y, x]]` with Perron root `x + y`.  `binom_gf` is exactly the statement
that its `L`-th power has trace-like total `(x + y) ^ L`, and the two evaluations
are

* `full_shift`: `Σ_a binom L a = 2 ^ L`  — the forward ambient measure;
* `reverse_branching`: `Σ_a binom L a · 3^(L−a) = 4 ^ L` — i.e. the reverse tree's
  branching factor is exactly `(4/3) ^ L`.  (`BackwardRange` §3 asserted this
  from a BFS; here it is a theorem.)

**The reverse operator is the forward operator tilted by `log₂ 3`.**  Writing the
forward tilted pressure as `P(x) = log₂(1 + x)` (weight `x` on a `1`), the reverse
pressure is `P_rev(x) = log₂(1 + x/3) = P(x/3)` — a shift of the tilt parameter by
exactly `log₂ 3`.  In `Nat` this is `binom_gf x 3`: `Σ_a binom L a xᵃ 3^(L−a) =
(x + 3)^L`, versus `binom_gf x 1`: `(x + 1)^L`.

So, precisely:

> `1 − H(log₃2)` is **a large-deviation rate, not a Perron eigenvalue and not a
> pressure zero.**  It is the Kullback–Leibler divergence `D(log₃2 ‖ 1/2)` in
> bits — the cost, under the uniform (Terras) measure on words, of the odd-step
> density being `log₃2` instead of `1/2`.  On the reverse side the same number is
> `D(log₃2 ‖ 1/4) − log₂(4/3)`, the cost under the branching measure (odd branch
> probability `(1/3)/(1 + 1/3) = 1/4`) of the same atypical density.  The two
> expressions are equal *because* `log₃2 · log₂3 = 1`.

**Against the Round III objection.**  Round III closed thermodynamic formalism
because `G` is not locally constant on the shift, so it is not a potential.  That
objection stands and this construction does not evade it.  The potential used
here is `ψ(w) = −a(w) log 3`, which *is* locally constant (one letter), and that
is exactly why it is harmless: it sees only `a`, never `C` or `G`.  The heavy
constraint itself is *not* sofic — `CycleLanguage.heavy_pad` shows every finite
block occurs in a heavy word, and `surplus_unbounded` below shows the surplus
`3^a / 2^i` along a heavy word is unbounded, so heaviness needs an unbounded
counter and no finite nonnegative matrix has `H(log₃2)` as its Perron root.  The
`1 × 1` operator above governs only the *ambient* measure; the exponent comes from
conditioning it, i.e. from the Legendre transform, which is why the answer is a
rate and not an eigenvalue.  So: the construction differs from the one Round III
killed by being about `a` alone, and that is precisely its limitation.

## 4. What a cycle is here, and why the duality cannot see it

A cycle of length `L` is simultaneously a closed forward orbit and a closed
reverse path.  In operator language it is a **periodic point of the shift**
`w = w₀…w_{L−1}` together with a *realisation*: the affine law makes
`(2^L − 3^a)·n = C(w)`, and `G = 2^L − 3^a` is odd, hence a unit in `ℤ₂`, so
**every periodic word already has a unique 2-adic fixed point `n = C(w)/G`.**  A
cycle is the event that this fixed point is a positive rational integer.

That is the whole answer, and it is negative.  The forward/reverse duality is a
statement about the pair `(L, a)`: `F_L` has one coefficient per `a`, both
evaluations are linear functionals of that coefficient vector
(`reverse_determined_by_forward`), and neither functional involves `C`.  But
`C(w) = Σ_{i=1..a} 3^(a−i) 2^(t_i)` is the coordinate a transfer operator
integrates out — it is not a function of `(L, a)`, and by
`CycleLanguage.heavy_pad` it is not a function of any bounded window either.  By
`NewModels.word_is_cycle_word` every word with positive gap *is* a cycle word of
`3x + δ(w)` with `δ(w) = G/gcd(C,G)`, so `(L, a)` never obstructs anything: the
obstruction is `δ(w) = 1`, and `δ` is invisible to both spectra.

Equivalently in the soundness filter's terms: both counts are `d`-free
(`C ↦ d·C` changes neither heaviness nor `a`), so by the Round III corrected
filter the whole duality is dead on arrival as a cycle obstruction.

## 5. Verdict

**The duality is real and vacuous.**  Real: `reverse_le_forward` and
`term_sandwich` are exact, and the shared object is `F_L`, the heavy language's
odd-step generating polynomial.  Vacuous: `F_L` is a function of `(L, a)` only,
`reverse_determined_by_forward` says the reverse count carries no information the
forward coefficients do not already carry, and `(L, a)` provably never obstructs.

The value of the closure is that it explains three rounds of coincidences in one
sentence: **every `0.05004` in this repository is `1 − H(log₃2) = D(log₃2 ‖ 1/2)`,
the large-deviation cost of the single inequality `2 ^ i ≤ 3 ^ a`, read once
forwards and once backwards.**  There is nothing else there.
-/

namespace Collatz
namespace ForwardReverse

open Collatz.Sum Collatz.CycleLanguage

/-! ## 0. Sum plumbing -/

/-- Pascal's triangle vanishes above the diagonal. -/
theorem binom_eq_zero_of_lt : ∀ {n k : Nat}, n < k → binom n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero => omega
      | succ k => rw [binom_succ_succ, ih (by omega), ih (by omega)]

/-- Peel the *first* term off a sum (`Core.Sum` only peels the last). -/
theorem sumRange_succ' (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  have h : n + 1 = 1 + n := by omega
  rw [h, sumRange_split, sumRange_one]
  refine congrArg _ (sumRange_congr (fun i _ => ?_))
  rw [Nat.add_comm]

/-- A constant factor comes out on the right. -/
theorem sumRange_mul_const (n c : Nat) (f : Nat → Nat) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  have h : (fun i => f i * c) = (fun i => c * f i) := by
    funext i; exact Nat.mul_comm _ _
  rw [h, sumRange_const_mul, Nat.mul_comm]

/-! ## 1. The one generating function

`gf L c x y = Σ_{a ≤ L} c a · xᵃ · y^(L−a)`.  Everything below is an evaluation
of this at two points. -/

/-- The generating polynomial of a coefficient vector `c` supported on `[0, L]`. -/
def gf (L : Nat) (c : Nat → Nat) (x y : Nat) : Nat :=
  sumRange (L + 1) (fun a => c a * x ^ a * y ^ (L - a))

theorem gf_def (L : Nat) (c : Nat → Nat) (x y : Nat) :
    gf L c x y = sumRange (L + 1) (fun a => c a * x ^ a * y ^ (L - a)) := rfl

/-- **The binomial theorem, in `Nat`, with no Mathlib.**  This is the transfer
operator of the free shift: the per-letter weights are `x` on a `1` and `y` on a
`0`, the operator is the rank-one matrix `[[y,x],[y,x]]`, its Perron root is
`x + y`, and the total weight at length `L` is `(x+y)^L`. -/
theorem binom_gf (x y : Nat) : ∀ L : Nat, gf L (binom L) x y = (x + y) ^ L := by
  intro L
  induction L with
  | zero => simp [gf, sumRange]
  | succ L ih =>
      rw [gf_def] at ih ⊢
      have hT2 : sumRange (L + 2) (fun b => binom L b * x ^ b * y ^ (L + 1 - b))
          = sumRange (L + 1) (fun b => binom L b * x ^ b * y ^ (L + 1 - b)) := by
        rw [sumRange_succ, binom_eq_zero_of_lt (Nat.lt_succ_self L)]
        simp
      have hTv : sumRange (L + 1) (fun b => binom L b * x ^ b * y ^ (L + 1 - b))
          = (x + y) ^ L * y := by
        rw [← ih, ← sumRange_mul_const]
        refine sumRange_congr (fun b hb => ?_)
        have he : L + 1 - b = (L - b) + 1 := by omega
        rw [he, Nat.pow_succ, ← Nat.mul_assoc]
      have hT1 : sumRange (L + 2) (fun b => binom L b * x ^ b * y ^ (L + 1 - b))
          = y ^ (L + 1)
            + sumRange (L + 1) (fun a => binom L (a + 1) * x ^ (a + 1) * y ^ (L - a)) := by
        rw [sumRange_succ' (L + 1)]
        have h0 : binom L 0 * x ^ 0 * y ^ (L + 1 - 0) = y ^ (L + 1) := by simp
        rw [h0]
        refine congrArg _ (sumRange_congr (fun a _ => ?_))
        have he : L + 1 - (a + 1) = L - a := by omega
        rw [he]
      rw [sumRange_succ' (L + 1)]
      have h0 : binom (L + 1) 0 * x ^ 0 * y ^ (L + 1 - 0) = y ^ (L + 1) := by simp
      have hstep : ∀ a : Nat,
          binom (L + 1) (a + 1) * x ^ (a + 1) * y ^ (L + 1 - (a + 1))
            = (binom L a * x ^ a * y ^ (L - a)) * x
              + (binom L (a + 1) * x ^ (a + 1) * y ^ (L - a)) := by
        intro a
        rw [binom_succ_succ]
        have he : L + 1 - (a + 1) = L - a := by omega
        rw [he, Nat.add_mul, Nat.add_mul]
        refine congrArg (· + binom L (a + 1) * x ^ (a + 1) * y ^ (L - a)) ?_
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm]
      rw [h0, sumRange_congr (fun a _ => hstep a), sumRange_add, sumRange_mul_const, ih]
      have hkey : y ^ (L + 1)
          + sumRange (L + 1) (fun a => binom L (a + 1) * x ^ (a + 1) * y ^ (L - a))
          = (x + y) ^ L * y := by rw [← hT1, hT2, hTv]
      have hfin : (x + y) ^ (L + 1) = (x + y) ^ L * x + (x + y) ^ L * y := by
        rw [Nat.pow_succ, Nat.mul_add]
      omega

/-- **Forward ambient measure.**  `Σ_a binom L a = 2 ^ L`: the full shift, the
Terras measure, one residue class mod `2 ^ L` per word. -/
theorem full_shift (L : Nat) : sumRange (L + 1) (binom L) = 2 ^ L := by
  have h := binom_gf 1 1 L
  rw [gf_def] at h
  rw [← h]
  exact (sumRange_congr (fun a _ => by simp)).symm

/-- **Reverse branching factor, exactly.**  `Σ_a binom L a · 3^(L−a) = 4 ^ L`,
i.e. the reverse tree grows by `(4/3)` per level, with odd-branch frequency
`(1/3)/(1+1/3) = 1/4`.  `BackwardRange` §3 measured this by BFS; it is a theorem. -/
theorem reverse_branching (L : Nat) :
    sumRange (L + 1) (fun a => binom L a * 3 ^ (L - a)) = 4 ^ L := by
  have h := binom_gf 1 3 L
  rw [gf_def] at h
  rw [← h]
  exact (sumRange_congr (fun a _ => by simp)).symm

/-- **The tilt shift, in `Nat`.**  The reverse operator is the forward operator
with the tilt parameter moved by `log₂ 3`: forward gives `(x+1)^L`, reverse gives
`(x+3)^L`, i.e. `P_rev(x) = P(x/3)`. -/
theorem tilt_shift (x L : Nat) :
    gf L (binom L) x 3 = (x + 3) ^ L ∧ gf L (binom L) x 1 = (x + 1) ^ L :=
  ⟨binom_gf x 3 L, binom_gf x 1 L⟩

/-! ## 2. Heaviness *is* the comparison of the forward and reverse densities -/

/-- **The support of the heavy count is the heavy inequality.**  A length-`L`
word with `a` ones that is heavy at every prefix — the last one included — exists
only when `2 ^ L ≤ 3 ^ a`.  This one line is the entire bridge: the left side is
the reciprocal forward density (Terras: one class mod `2^L`), the right side is
the reciprocal reverse density (`endpoint_class`: one class mod `3^a`). -/
theorem heavy_support : ∀ {L a : Nat}, heavyCount L a ≠ 0 → 2 ^ L ≤ 3 ^ a := by
  intro L a h
  cases L with
  | zero =>
      cases a with
      | zero => exact Nat.le_refl 1
      | succ a => exact absurd rfl h
  | succ L =>
      cases a with
      | zero => exact absurd rfl h
      | succ a =>
          rw [heavyCount_succ_succ] at h
          by_cases hc : 2 ^ (L + 1) ≤ 3 ^ (a + 1)
          · exact hc
          · rw [if_neg hc] at h; exact absurd rfl h

/-- A heavy word cannot have more ones than letters. -/
theorem heavy_le_length {L a : Nat} (h : heavyCount L a ≠ 0) : a ≤ L := by
  rcases Nat.lt_or_ge L a with hlt | hge
  · have h1 := heavyCount_le_binom L a
    rw [binom_eq_zero_of_lt hlt] at h1
    omega
  · exact hge

/-- The number of `x` in a window of size `2^L · 3^a` carrying a prescribed
length-`L` parity word: by Terras the word pins `x` mod `2 ^ L`, so it is `3 ^ a`. -/
def fwdWindow (_L a : Nat) : Nat := 3 ^ a

/-- The number of endpoints `y` in the same window above which that word is
realised: by `BackwardRange.endpoint_class` the endpoints form one class mod
`3 ^ a`, so it is `2 ^ L`. -/
def revWindow (L _a : Nat) : Nat := 2 ^ L

/-- The two windows are read against the same modulus `2^L · 3^a`. -/
theorem window_common (L a : Nat) : fwdWindow L a * 2 ^ L = revWindow L a * 3 ^ a := by
  rw [fwdWindow, revWindow]
  exact Nat.mul_comm _ _

/-- **Heaviness is exactly "the reverse class is no denser than the forward
class".**  A restatement, not a discovery — but it is *the* restatement: the
forward heavy condition and the reverse density condition are literally the same
inequality `2 ^ L ≤ 3 ^ a`, which is why the two counting exponents cannot fail
to agree. -/
theorem heavy_iff_rev_le_fwd (L a : Nat) :
    2 ^ L ≤ 3 ^ a ↔ revWindow L a ≤ fwdWindow L a := Iff.rfl

/-! ## 3. The two evaluations, and the sandwich -/

/-- The forward count: the number of heavy words of length `L`. -/
def heavyTotal (L : Nat) : Nat := gf L (heavyCount L) 1 1

/-- The reverse weight, cleared of denominators: `3 ^ L · Σ_a heavyCount L a · 3^(−a)`. -/
def revWeight (L : Nat) : Nat := gf L (heavyCount L) 1 3

theorem heavyTotal_eq (L : Nat) : heavyTotal L = sumRange (L + 1) (heavyCount L) := by
  rw [heavyTotal, gf_def]
  exact sumRange_congr (fun a _ => by simp)

theorem revWeight_eq (L : Nat) :
    revWeight L = sumRange (L + 1) (fun a => heavyCount L a * 3 ^ (L - a)) := by
  rw [revWeight, gf_def]
  exact sumRange_congr (fun a _ => by simp)

/-- Splitting `3 ^ L` at a point below `L`. -/
theorem three_split {L a : Nat} (h : a ≤ L) : 3 ^ a * 3 ^ (L - a) = 3 ^ L := by
  rw [← Nat.pow_add]
  exact congrArg _ (by omega)

/-- **The termwise duality, exact.**  At an odd-step count `a` that is *critical*
— heavy (`2^L ≤ 3^a`) and minimally so (`3^a ≤ 3·2^L`) — the reverse weight
`3^(−a)` and the forward weight `2^(−L)` agree to within a factor of three, for
any coefficient `N` whatsoever.  This is the precise, asymptotics-free content of
"the two counts are one object": at the binding density the two weightings
coincide, and the binding density is the same on both sides because the
constraint is the same inequality. -/
theorem term_le {L a N : Nat} (hle : a ≤ L) (h1 : 2 ^ L ≤ 3 ^ a) :
    2 ^ L * (N * 3 ^ (L - a)) ≤ 3 ^ L * N := by
  have hs := three_split hle
  have hm : 2 ^ L * 3 ^ (L - a) ≤ 3 ^ a * 3 ^ (L - a) := Nat.mul_le_mul_right _ h1
  calc 2 ^ L * (N * 3 ^ (L - a)) = (2 ^ L * 3 ^ (L - a)) * N := by
        rw [Nat.mul_comm N, ← Nat.mul_assoc]
    _ ≤ (3 ^ a * 3 ^ (L - a)) * N := Nat.mul_le_mul_right _ hm
    _ = 3 ^ L * N := by rw [hs]

/-- The matching lower half, at a *critical* `a` (`3^a ≤ 3·2^L`). -/
theorem term_ge {L a N : Nat} (hle : a ≤ L) (h2 : 3 ^ a ≤ 3 * 2 ^ L) :
    3 ^ L * N ≤ 3 * (2 ^ L * (N * 3 ^ (L - a))) := by
  have hs := three_split hle
  have hm : 3 ^ a * 3 ^ (L - a) ≤ (3 * 2 ^ L) * 3 ^ (L - a) := Nat.mul_le_mul_right _ h2
  calc 3 ^ L * N = (3 ^ a * 3 ^ (L - a)) * N := by rw [hs]
    _ ≤ ((3 * 2 ^ L) * 3 ^ (L - a)) * N := Nat.mul_le_mul_right _ hm
    _ = 3 * (2 ^ L * (N * 3 ^ (L - a))) := by
        rw [Nat.mul_comm N, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_assoc 3]

/-- The two halves together. -/
theorem term_sandwich {L a N : Nat} (hle : a ≤ L) (h1 : 2 ^ L ≤ 3 ^ a)
    (h2 : 3 ^ a ≤ 3 * 2 ^ L) :
    2 ^ L * (N * 3 ^ (L - a)) ≤ 3 ^ L * N
      ∧ 3 ^ L * N ≤ 3 * (2 ^ L * (N * 3 ^ (L - a))) :=
  ⟨term_le hle h1, term_ge hle h2⟩

/-- **Minimality gives the second hypothesis of `term_sandwich`.**  If `a+1` is
the least exponent with `2^L ≤ 3^(a+1)` then automatically `3^(a+1) ≤ 3·2^L`.
So the critical density really is critical: the sandwich applies at the smallest
heavy `a`, which is the term that dominates both sums. -/
theorem min_heavy_bound {L a : Nat} (h2 : ¬ (2 ^ L ≤ 3 ^ a)) :
    3 ^ (a + 1) ≤ 3 * 2 ^ L := by
  have h : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ]; omega
  omega

/-- **The duality, summed: the reverse weight never exceeds the forward count.**
`2 ^ L · revWeight L ≤ 3 ^ L · heavyTotal L`, i.e. `Σ_a hᵃ·3^(−a) ≤ 2^(−L)·Σ_a hᵃ`.
Proved termwise from `heavy_support`: heaviness *is* `3^(−a) ≤ 2^(−L)`.  The
matching lower bound holds at the critical term (`term_sandwich`) and, measured,
for the whole sum with a constant in `[2^(−3.41), 2^(−2.44)]` for
`L = 40 … 4701`; that constant is a dominated-convergence fact about the
geometric decay of `hᵃ` in `a`, not proved here. -/
theorem reverse_le_forward (L : Nat) :
    2 ^ L * revWeight L ≤ 3 ^ L * heavyTotal L := by
  rw [revWeight_eq, heavyTotal_eq, ← sumRange_const_mul, ← sumRange_const_mul]
  refine sumRange_le (fun a _ => ?_)
  by_cases h : heavyCount L a = 0
  · rw [h]; simp
  · exact term_le (heavy_le_length h) (heavy_support h)

/-! ## 4. The vacuity: the duality is a function of `(L, a)` and nothing else -/

/-- **The reverse count carries no information the forward coefficients do not.**
Any two coefficient vectors agreeing on `[0, L]` give the same generating value
at every `(x, y)`.  Since `heavyCount L a` depends only on `(L, a)`, both the
forward count and the reverse weight are functions of `(L, a)` alone: neither can
see `C(w)`, `G`, or `δ(w)`. -/
theorem reverse_determined_by_forward {L x y : Nat} {c c' : Nat → Nat}
    (h : ∀ a, a ≤ L → c a = c' a) : gf L c x y = gf L c' x y := by
  rw [gf_def, gf_def]
  exact sumRange_congr (fun a ha => by rw [h a (by omega)])

/-- Specialised: the forward count determines the reverse weight outright. -/
theorem revWeight_of_heavyTotal_data {L : Nat} {c : Nat → Nat}
    (h : ∀ a, a ≤ L → c a = heavyCount L a) : gf L c 1 3 = revWeight L :=
  reverse_determined_by_forward h

/-- **The heavy constraint needs an unbounded counter.**  For every bound `B`
there is a heavy prefix whose surplus `3^a / 2^i` exceeds `B`: take `2B` ones,
where `2 ^ (2B) · B ≤ 3 ^ (2B)`.  Hence no finite nonnegative matrix has
`H(log₃ 2)` as its Perron root, and `1 − H(log₃ 2)` is a large-deviation rate,
not an eigenvalue.  (`CycleLanguage.heavy_pad` is the companion fact: no
forbidden block exists either, so the language is not sofic in either direction.) -/
theorem surplus_unbounded (B : Nat) : 2 ^ (2 * B) * B ≤ 3 ^ (2 * B) := by
  have hB : B ≤ 2 ^ B := Nat.le_of_lt Nat.lt_two_pow_self
  have h1 : 2 ^ (2 * B) * B ≤ 2 ^ (2 * B) * 2 ^ B :=
    Nat.mul_le_mul_left _ hB
  have h2 : (2 : Nat) ^ (2 * B) * 2 ^ B = 8 ^ B := by
    rw [← Nat.pow_add, show 2 * B + B = 3 * B from by omega, Nat.pow_mul]
  have h3 : (3 : Nat) ^ (2 * B) = 9 ^ B := by rw [Nat.pow_mul]
  have h4 : (8 : Nat) ^ B ≤ 9 ^ B := Nat.pow_le_pow_left (by decide) B
  omega

/-! ## 5. The verdict, as one theorem -/

/-- **Forward and reverse are one object, and the object is `(L, a)`.**

1. one generating function, two evaluations: `heavyTotal L = gf L (heavyCount L) 1 1`
   and `revWeight L = gf L (heavyCount L) 1 3` — true by definition, which is the
   point;
2. the reverse weight is bounded by the forward count with the exact factor
   `2^(−L)`, termwise from heaviness alone;
3. the reverse weight is a function of the forward coefficients;
4. and the heavy constraint is not finite-state, so the shared exponent is a
   large-deviation rate.

None of (1)–(4) mentions `C(w)`.  By `NewModels.word_is_cycle_word` every word
with a positive gap is a cycle word of `3x + δ(w)`, so no statement about
`(L, a)` alone can obstruct a cycle.  **The duality is real and vacuous.** -/
theorem forward_reverse_duality (L : Nat) :
    heavyTotal L = gf L (heavyCount L) 1 1
      ∧ revWeight L = gf L (heavyCount L) 1 3
      ∧ 2 ^ L * revWeight L ≤ 3 ^ L * heavyTotal L
      ∧ (∀ c : Nat → Nat, (∀ a, a ≤ L → c a = heavyCount L a) → gf L c 1 3 = revWeight L)
      ∧ (∀ B : Nat, 2 ^ (2 * B) * B ≤ 3 ^ (2 * B)) :=
  ⟨rfl, rfl, reverse_le_forward L, fun _ h => revWeight_of_heavyTotal_data h,
    surplus_unbounded⟩

end ForwardReverse
end Collatz
