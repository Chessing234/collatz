import Collatz.Structure.DensityRate
import Collatz.Strategy.AffineExact

/-!
# The tilted weight, and the last constant the counting argument can give

`Density`, `DensitySharp` and `DensityRate` all run the same argument.  Each
residue `r < 2 ^ k` is given the weight `2 ^ a(r,k)`, the total weight is
`3 ^ k` exactly, heaviness forces `a ≥ p k / q` for any fraction `p/q` with
`3 ^ p < 2 ^ q`, and comparing `2 ^ ⌈pk/q⌉ · heavyCount k` against `3 ^ k` gives

`heavyCount k ^ q · (2 ^ p) ^ k ≤ (3 ^ q) ^ k`.

Improving the fraction improved the exponent: `3/5` gives `0.98496`, `17/27`
gives `0.95533`, `41/65` gives `0.95419`.  But `DensityRate` also records the
ceiling of that family — even a perfect fraction `p/q → log 2 / log 3` only
reaches `log₂ 3 − 1 − log 2 / log 3 = 0.95403`.  The fraction is not what is
holding the argument back.  The **weight** is.

## What is actually being optimised

The weight `2 ^ a` is one member of a two-parameter family: give a residue with
`a` odd steps and `k − a` even steps the weight `t ^ a · s ^ (k − a)`.  The
pairing lemma of `Density` — of the two residues `r` and `2 ^ k + r` exactly one
takes an odd step at time `k`, because `3 ^ a` is odd — says the two children of
a level-`k` residue have weights `t` and `s` times their parent's.  So the total
weight satisfies `W(k+1) = (t + s) · W(k)`, hence

`Σ_{r < 2^k} t ^ a(r,k) · s ^ (k − a(r,k)) = (t + s) ^ k`   (`tiltSum_eq`).

The old weight is the case `(t, s) = (2, 1)`: total `3 ^ k`, as before.  Nothing
in the identity prefers that choice.

Now push the same comparison through.  Heaviness gives `a ≥ pk/q`, the weight is
increasing in `a` once `s ≤ t`, so every heavy residue carries at least
`t ^ ⌈pk/q⌉ · s ^ (k − ⌈pk/q⌉)`, and the `q`-th power of that is at least
`(t ^ p · s ^ (q − p)) ^ k`.  The conclusion is

`heavyCount k ^ q · (t ^ p · s ^ (q − p)) ^ k ≤ ((t + s) ^ q) ^ k`,

i.e. `heavyCount k ≲ ((t + s) ^ q / (t ^ p s ^ (q−p))) ^ (k/q)`.  The bracket is
a Chernoff bound with tilt `t/s`, and elementary calculus — which we do not need
to formalise, only to *choose* by — puts its minimum at `t / s = p / (q − p)`.
The old weight `2 ^ a = 2 ^ a · 1 ^ (k−a)` is the tilt `2/1`, which is the
optimum for the rate `2/3` — a rate this argument cannot even use, since
`3 ^ 2 = 9 > 8 = 2 ^ 3`.  **The weight was tuned to a fraction that does not
exist.**  That mismatch, not the choice of `p/q`, is what the earlier files were
paying for.

## The instances

Matching the tilt to the rate:

| rate `p/q` | tilt `t/s` | statement | exponent |
|---|---|---|---|
| `3/5` | `2/1` (old) | `hc ^ 5 · 8 ^ k ≤ 243 ^ k` | `0.98496` |
| `3/5` | `3/2` | `hc ^ 5 · (3^3 2^2) ^ k ≤ (5^5) ^ k` | `0.97095` |
| `17/27` | `2/1` (old) | `hc ^ 27 · (2^17) ^ k ≤ (3^27) ^ k` | `0.95533` |
| `17/27` | `17/10` | `hc ^ 27 · (17^17 10^10) ^ k ≤ (27^27) ^ k` | `0.95096` |
| `41/65` | `41/24` | `hc ^ 65 · (41^41 24^24) ^ k ≤ (65^65) ^ k` | `0.95008` |
| optimum | — | — | `0.94996` |

The headline is `heavyCount_pow_twentyseven_tilted`.  Matching the tilt to the
existing rate `17/27` buys more (`0.95533 → 0.95096`) than the entire jump from
`3/5` to a perfect fraction ever could (`0.98496 → 0.95403`), and it does so
with the *same* two arithmetic facts the repo already owns: the pairing lemma,
and `3 ^ 17 = 129140163 < 134217728 = 2 ^ 27`.

That last inequality is exactly what licenses the tilt.  The tilt `17/10` is
only useful if the rate `17/27` is available, and the rate `17/27` is available
only because `3 ^ 17` slips under `2 ^ 27` — by `0.038%`.  Every constant in
`17 ^ 17 · 10 ^ 10 ≤ 27 ^ 27 / heavyCount`-shaped bound descends from that one
near-miss.  The neighbouring convergent `12/19` fails
(`3 ^ 12 = 531441 > 524288 = 2 ^ 19`), and with it the tilt `12/7`.

## What is proved, and what is not

Proved: the tilted weight identity for every `(t, s)`, the monotonicity of the
tilted weight in `a`, the per-residue power bound, the general theorem
`heavyCount_pow_tilt`, and the four instances above.  `0.95096` is a genuine
strengthening of every density bound previously in the repo; the two constants
are compared head to head in `tilted_beats_untilted`, and the two rates in
`seventeen_beats_three`.

Not proved, and not provable here: that the optimal tilt is optimal.  The table
above chooses `t/s = p/(q−p)` on the strength of a real-variable computation
performed outside Lean; what is formalised is only that each chosen pair works.
Nor is any *lower* bound on `heavyCount` proved — this file says the heavy set
thins, never that it survives.  It does survive: `2 ^ k − 1` is heavy at every
level (`Density.heavy_two_pow_sub_one`), so the exponent could be driven to the
information-theoretic floor `0.94996` and the conjecture would be exactly as far
away.  The value of the sharpening is that it exhausts the method visibly.  At
`0.95096` against a floor of `0.94996` there is `0.001` of room left in the
entire counting argument, and no arrangement of weights or fractions can find
more than that.
-/

namespace Collatz
namespace DensitySharper

open Reach Congruence _root_.Collatz.Sum Density

/-! ## The tilted weight

A residue is weighted by `t` for each odd step and `s` for each even step.  The
old weight is `(t, s) = (2, 1)`. -/

/-- `tiltWeight t s k r = t ^ a(r,k) · s ^ (k − a(r,k))`. -/
def tiltWeight (t s k r : Nat) : Nat := t ^ oddCount r k * s ^ (k - oddCount r k)

/-- `tiltSum t s k = Σ_{r < 2^k} tiltWeight t s k r`. -/
def tiltSum (t s k : Nat) : Nat := sumRange (2 ^ k) (tiltWeight t s k)

/-- The two-term collapse behind the pairing lemma: a residue whose child takes
an even step contributes `s` times the parent weight, the one whose child takes
an odd step contributes `t` times, and together `t + s`. -/
theorem tilt_two {t s a k : Nat} (hak : a ≤ k) :
    t ^ a * s ^ (k + 1 - a) + t ^ (a + 1) * s ^ (k + 1 - (a + 1))
      = (t + s) * (t ^ a * s ^ (k - a)) := by
  have e1 : k + 1 - a = (k - a) + 1 := by omega
  have e2 : k + 1 - (a + 1) = k - a := by omega
  rw [e1, e2, Nat.pow_succ, Nat.pow_succ]
  simp only [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  omega

/-- **The tilted pairing lemma.**  Exactly one of `r` and `2 ^ k + r` takes an
odd step at time `k`, so their level-`(k+1)` weights sum to `(t + s)` times the
common level-`k` weight.  This is `Density.weight_pair` with `2 ^ a` replaced by
`t ^ a s ^ (k−a)`; the mechanism — `3 ^ a` is odd, so shifting by the modulus
flips the parity of the `k`-th iterate — is identical. -/
theorem tilt_pair (t s : Nat) (r k : Nat) (hr : r < 2 ^ k) :
    tiltWeight t s (k + 1) r + tiltWeight t s (k + 1) (2 ^ k + r)
      = (t + s) * tiltWeight t s k r := by
  have hshift : oddCount (2 ^ k + r) k = oddCount r k := oddCount_two_pow_add hr
  have horb : acceleratedOrbit k (2 ^ k + r) = 3 ^ oddCount r k + acceleratedOrbit k r :=
    accOrbit_two_pow_add r k
  have hodd : 3 ^ oddCount r k % 2 = 1 := Arith.three_pow_odd _
  have hak : oddCount r k ≤ k := AffineExact.oddCount_le_self r k
  simp only [tiltWeight]
  rw [oddCount_succ_last, oddCount_succ_last, hshift, horb]
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k r) with he | ho
  · have h1 : (3 ^ oddCount r k + acceleratedOrbit k r) % 2 = 1 := by omega
    rw [he, h1]
    simp only [Nat.add_zero]
    exact tilt_two hak
  · have h1 : (3 ^ oddCount r k + acceleratedOrbit k r) % 2 = 0 := by omega
    rw [ho, h1]
    simp only [Nat.add_zero]
    have := tilt_two (t := t) (s := s) hak
    omega

/-- **The tilted weight identity.**  `Σ_{r < 2^k} t ^ a(r,k) · s ^ (k−a(r,k))
= (t + s) ^ k`, for every `t` and `s`.  At `(t, s) = (2, 1)` this is
`Density.weightSum_eq`. -/
theorem tiltSum_eq (t s : Nat) : ∀ k : Nat, tiltSum t s k = (t + s) ^ k := by
  intro k
  induction k with
  | zero => simp [tiltSum, tiltWeight]
  | succ k ih =>
    have hsplit : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
    rw [tiltSum, hsplit, sumRange_two_mul]
    have hcombine :
        sumRange (2 ^ k) (tiltWeight t s (k + 1))
          + sumRange (2 ^ k) (fun i => tiltWeight t s (k + 1) (2 ^ k + i))
        = sumRange (2 ^ k) (fun r => (t + s) * tiltWeight t s k r) := by
      rw [← sumRange_add]
      exact sumRange_congr (fun i hi => tilt_pair t s i k hi)
    rw [hcombine, sumRange_const_mul]
    have hih : sumRange (2 ^ k) (tiltWeight t s k) = (t + s) ^ k := ih
    rw [hih, Nat.pow_succ, Nat.mul_comm]

/-! ## Monotonicity and the power bound -/

/-- The tilted weight increases with the odd-step count, provided `s ≤ t`. -/
theorem tiltWeight_mono {t s a b k : Nat} (hst : s ≤ t) (hab : a ≤ b) (hbk : b ≤ k) :
    t ^ a * s ^ (k - a) ≤ t ^ b * s ^ (k - b) := by
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, k = b + c := ⟨k - b, by omega⟩
  have e1 : k - a = d + c := by omega
  have e2 : k - b = c := by omega
  have hpow : s ^ d ≤ t ^ d := Nat.pow_le_pow_left hst d
  rw [e1, e2, hd, Nat.pow_add, Nat.pow_add]
  calc t ^ a * (s ^ d * s ^ c) ≤ t ^ a * (t ^ d * s ^ c) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
    _ = t ^ a * t ^ d * s ^ c := by rw [Nat.mul_assoc]

/-- **The per-residue power bound.**  If the odd-step count `a` clears the rate
`p/(p+m)`, the `(p+m)`-th power of its tilted weight is at least
`(t ^ p s ^ m) ^ k`.

The slack is where the tilt pays: writing `d = (p+m)a − pk ≥ 0`, the power equals
`(t ^ p s ^ m) ^ k · (t/s) ^ d`, and `s ≤ t` makes that factor harmless.  With
the untilted weight `s = 1` the same factor is `t ^ d`, which is larger — but the
base `(t ^ p s ^ m) ^ k` it multiplies is correspondingly worse, and it is the
base that controls the exponent. -/
theorem tilt_pow_le {t s p m a k : Nat} (hst : s ≤ t) (hak : a ≤ k)
    (hpk : p * k ≤ (p + m) * a) :
    t ^ (p * k) * s ^ (m * k) ≤ (t ^ a * s ^ (k - a)) ^ (p + m) := by
  obtain ⟨c, hc⟩ : ∃ c, k = a + c := ⟨k - a, by omega⟩
  have hka : k - a = c := by omega
  have h1 : p * k = p * a + p * c := by rw [hc, Nat.mul_add]
  have h2 : (p + m) * a = p * a + m * a := by rw [Nat.add_mul]
  have hpc : p * c ≤ m * a := by omega
  obtain ⟨d, hd⟩ : ∃ d, m * a = p * c + d := ⟨m * a - p * c, by omega⟩
  have hRHS : (t ^ a * s ^ (k - a)) ^ (p + m)
      = t ^ (p * a + p * c + d) * s ^ (p * c + m * c) := by
    rw [hka, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    have ea : a * (p + m) = p * a + p * c + d := by
      rw [Nat.mul_add, Nat.mul_comm a p, Nat.mul_comm a m]; omega
    have ec : c * (p + m) = p * c + m * c := by
      rw [Nat.mul_add, Nat.mul_comm c p, Nat.mul_comm c m]
    rw [ea, ec]
  have hLHS : t ^ (p * k) * s ^ (m * k)
      = t ^ (p * a + p * c) * (s ^ (p * c + m * c) * s ^ d) := by
    have e2 : m * k = (p * c + m * c) + d := by rw [hc, Nat.mul_add]; omega
    rw [h1, e2, Nat.pow_add s (p * c + m * c) d]
  have hpow : s ^ d ≤ t ^ d := Nat.pow_le_pow_left hst d
  rw [hLHS, hRHS]
  calc t ^ (p * a + p * c) * (s ^ (p * c + m * c) * s ^ d)
      ≤ t ^ (p * a + p * c) * (s ^ (p * c + m * c) * t ^ d) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow)
    _ = t ^ (p * a + p * c + d) * s ^ (p * c + m * c) := by
        rw [Nat.pow_add t (p * a + p * c) d]
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-! ## The counting step -/

/-- The minimal odd-step count a heavy residue can have, `⌈pk/q⌉`. -/
def minOdd (p q k : Nat) : Nat := (p * k + (q - 1)) / q

/-- Every heavy residue carries at least the tilted weight of `⌈pk/q⌉`. -/
theorem tiltWeight_le_of_heavy {p m t s : Nat} (hst : s ≤ t)
    (hpq : 3 ^ p < 2 ^ (p + m)) (hq : 0 < p + m) {k r : Nat} (h : heavyB k r = true) :
    t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k) ≤ tiltWeight t s k r := by
  have hheavy : 2 ^ k ≤ 3 ^ oddCount r k := by simpa [heavyB] using h
  have hrate : p * k ≤ (p + m) * oddCount r k :=
    DensityRate.mul_le_mul_of_heavy hpq hheavy
  have hmin : minOdd p (p + m) k ≤ oddCount r k :=
    DensityRate.ceil_div_le hq hrate
  have hak : oddCount r k ≤ k := AffineExact.oddCount_le_self r k
  exact tiltWeight_mono hst hmin hak

/-- The counted weight bound at the tilt `t/s` and the rate `p/(p+m)`. -/
theorem mul_heavyCount_le_tilt {p m t s : Nat} (hst : s ≤ t)
    (hpq : 3 ^ p < 2 ^ (p + m)) (hq : 0 < p + m) (k : Nat) :
    (t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) * heavyCount k
      ≤ (t + s) ^ k := by
  have h := mul_countRange_le (n := 2 ^ k)
    (w := t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k))
    (p := heavyB k) (f := tiltWeight t s k)
    (fun i _ hi => tiltWeight_le_of_heavy hst hpq hq hi)
  have hw : sumRange (2 ^ k) (tiltWeight t s k) = (t + s) ^ k := tiltSum_eq t s k
  rw [heavyCount]
  omega

/-! ## The theorem -/

/-- **The tilted density theorem.**  For any tilt `s ≤ t` and any rate `p/(p+m)`
admissible in the sense `3 ^ p < 2 ^ (p+m)`,

`heavyCount k ^ (p+m) · (t ^ p · s ^ m) ^ k ≤ ((t + s) ^ (p+m)) ^ k`.

At `(t, s) = (2, 1)` this is `DensityRate.heavyCount_pow`.  The gain comes from
choosing `t/s = p/m`, matching the tilt to the rate. -/
theorem heavyCount_pow_tilt {p m t s : Nat} (hst : s ≤ t)
    (hpq : 3 ^ p < 2 ^ (p + m)) (hq : 0 < p + m) (k : Nat) :
    heavyCount k ^ (p + m) * (t ^ p * s ^ m) ^ k ≤ ((t + s) ^ (p + m)) ^ k := by
  have hbase := mul_heavyCount_le_tilt hst hpq hq k
  have hpow :
      ((t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) * heavyCount k) ^ (p + m)
        ≤ ((t + s) ^ k) ^ (p + m) := Nat.pow_le_pow_left hbase (p + m)
  have hleft :
      ((t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) * heavyCount k) ^ (p + m)
        = (t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) ^ (p + m)
            * heavyCount k ^ (p + m) := by
    rw [Nat.mul_pow]
  have hright : ((t + s) ^ k) ^ (p + m) = ((t + s) ^ (p + m)) ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  -- the minimal heavy weight already beats `(t ^ p s ^ m) ^ k` after `q`-th powers
  have hmin_le : minOdd p (p + m) k ≤ k := by
    refine DensityRate.ceil_div_le hq ?_
    exact Nat.mul_le_mul_right k (by omega)
  have hmin_rate : p * k ≤ (p + m) * minOdd p (p + m) k :=
    DensityRate.le_mul_ceil_div (p * k) (p + m) hq
  have hterm : t ^ (p * k) * s ^ (m * k)
      ≤ (t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) ^ (p + m) :=
    tilt_pow_le hst hmin_le hmin_rate
  have hbaseeq : (t ^ p * s ^ m) ^ k = t ^ (p * k) * s ^ (m * k) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  rw [hleft, hright] at hpow
  calc heavyCount k ^ (p + m) * (t ^ p * s ^ m) ^ k
      = heavyCount k ^ (p + m) * (t ^ (p * k) * s ^ (m * k)) := by rw [hbaseeq]
    _ ≤ heavyCount k ^ (p + m)
          * (t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) ^ (p + m) :=
        Nat.mul_le_mul_left _ hterm
    _ = (t ^ minOdd p (p + m) k * s ^ (k - minOdd p (p + m) k)) ^ (p + m)
          * heavyCount k ^ (p + m) := Nat.mul_comm _ _
    _ ≤ ((t + s) ^ (p + m)) ^ k := hpow

/-! ## The instances

Four points of the two-parameter family, each an instance of the same theorem. -/

/-- The old bound recovered: rate `3/5`, tilt `2/1`.  This is
`Density.heavyCount_pow_five` up to the normal forms `2 ^ 3 = 8`, `3 ^ 5 = 243`. -/
theorem rate_three_five_untilted (k : Nat) :
    heavyCount k ^ 5 * (2 ^ 3 * 1 ^ 2) ^ k ≤ (3 ^ 5) ^ k :=
  heavyCount_pow_tilt (p := 3) (m := 2) (t := 2) (s := 1) (by omega) (by decide) (by omega) k

/-- Rate `3/5` with its own optimal tilt `3/2`: `heavyCount k ^ 5 · 108 ^ k ≤
3125 ^ k`, exponent `0.97095` against the `0.98496` of `Density.
heavyCount_pow_five`.  The fraction is unchanged; only the weight moved. -/
theorem rate_three_five_tilted (k : Nat) :
    heavyCount k ^ 5 * (3 ^ 3 * 2 ^ 2) ^ k ≤ (5 ^ 5) ^ k :=
  heavyCount_pow_tilt (p := 3) (m := 2) (t := 3) (s := 2) (by omega) (by decide) (by omega) k

/-- The inequality that licenses the rate `17/27`, and with it the tilt `17/10`:
`3 ^ 17 = 129140163 < 134217728 = 2 ^ 27`. -/
theorem seventeen_twentyseven_holds : (3:Nat) ^ 17 < 2 ^ (17 + 10) := by decide

/-- **The headline.**  Rate `17/27` at its optimal tilt `17/10`:

`heavyCount k ^ 27 · (17 ^ 17 · 10 ^ 10) ^ k ≤ (27 ^ 27) ^ k`,

i.e. `heavyCount k ≤ 2 ^ (0.95096 k)`, against `0.95533` for the same rate
untilted and `0.98496` for the bound the repo started with.  The
information-theoretic floor for the heavy count is `0.94996`. -/
theorem heavyCount_pow_twentyseven_tilted (k : Nat) :
    heavyCount k ^ 27 * (17 ^ 17 * 10 ^ 10) ^ k ≤ (27 ^ 27) ^ k :=
  heavyCount_pow_tilt (p := 17) (m := 10) (t := 17) (s := 10)
    (by omega) seventeen_twentyseven_holds (by omega) k

/-- The next convergent, `41/65`, at its optimal tilt `41/24`, giving `0.95008`
— within `1.2 · 10 ^ (−4)` of the floor.  The licensing inequality is
`3 ^ 41 = 36472996377170786403 < 36893488147419103232 = 2 ^ 65`. -/
theorem heavyCount_pow_sixtyfive_tilted (k : Nat) :
    heavyCount k ^ 65 * (41 ^ 41 * 24 ^ 24) ^ k ≤ (65 ^ 65) ^ k :=
  heavyCount_pow_tilt (p := 41) (m := 24) (t := 41) (s := 24)
    (by omega) (by decide) (by omega) k

/-! ## Comparison with what was there before -/

/-- **The tilt is a strict gain, at the same rate.**  Both bounds say
`heavyCount k ^ 27 ≤ R ^ k` for a ratio `R`; the untilted one has
`R = 3 ^ 27 / 2 ^ 17`, the tilted one `R = 27 ^ 27 / (17 ^ 17 · 10 ^ 10)`.
Cleared of denominators, the tilted ratio is the smaller.  Neither statement
implies the other term by term — they are two instances of
`heavyCount_pow_tilt` — but this inequality is what makes the tilted one the
better bound for every `k`. -/
theorem tilted_beats_untilted :
    27 ^ 27 * (2:Nat) ^ 17 < 3 ^ 27 * (17 ^ 17 * 10 ^ 10) := by decide

/-- And the tilted `17/27` bound beats the tilted `3/5` bound, comparing the two
per-step ratios at the common exponent `135 = 5 · 27`:
`(27 ^ 27 / 17 ^ 17 10 ^ 10) ^ 5 < (5 ^ 5 / 3 ^ 3 2 ^ 2) ^ 27`. -/
theorem seventeen_beats_three :
    (27 ^ 27) ^ 5 * ((3:Nat) ^ 3 * 2 ^ 2) ^ 27 < (5 ^ 5) ^ 27 * (17 ^ 17 * 10 ^ 10) ^ 5 := by
  decide

/-- The heavy set is still nonempty at every level, so none of this bears on the
conjecture: `2 ^ k − 1` is heavy for every `k > 0`. -/
theorem sharper_but_still_nonempty {k : Nat} (hk : 0 < k) :
    0 < heavyCount k ∧
      heavyCount k ^ 27 * (17 ^ 17 * 10 ^ 10) ^ k ≤ (27 ^ 27) ^ k :=
  ⟨heavyCount_pos hk, heavyCount_pow_twentyseven_tilted k⟩

end DensitySharper
end Collatz
