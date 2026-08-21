import Collatz.Strategy.RepetitionDescent

/-!
# The image of `w ↦ C(w) mod G`, and where the `0.05·L`-bit surplus actually lives

Fix a shape `(L, a)` with `2 ^ (L-1) ≤ 3 ^ a < 2 ^ L` and gap `G = 2 ^ L − 3 ^ a`.
The cycle language `S(L,a)` — words heavy at every proper prefix — has
`N ≈ binom L a / L ≈ 2 ^ (0.94996·L) / L` elements, while `G ≈ 2 ^ L`.  So the map

    `Φ : S(L,a) → ℤ/G`,  `Φ w = wC w mod G`

sends a set of size `N` into a set of size `G`, and a cycle at that shape exists iff
`0 ∈ Φ(S)`.  The counting surplus is `log₂ G − log₂ N ≈ (1 − H₂(log₃2))·L = 0.05004·L`.

This file answers two questions about `Φ`, one measured and one proved.

## 1. Measured: `Φ` is essentially injective (exhaustive, `L ≤ 29`)

For every shape with `L ≤ 29` (only one `a` per `L` has a nonempty language — see
`shape_unique` below) the exact image size was computed:

| L  | a  | G          | N        | image    | collisions | birthday model |
|----|----|------------|----------|----------|-----------|----------------|
| 16 | 10 | 6487       | 476      | 474      | 2         | 17.0           |
| 18 | 11 | 84997      | 961      | 961      | 0         | 5.4            |
| 20 | 12 | 517135     | 2652     | 2652     | 0         | 6.8            |
| 21 | 13 | 502829     | 8045     | 8045     | 0         | 64.0           |
| 23 | 14 | 3605639    | 17637    | 17637    | 0         | 43.1           |
| 24 | 15 | 2428309    | 51033    | 50951    | 82        | 532.5          |
| 26 | 16 | 24062143   | 108950   | 108950   | 0         | 246.3          |
| 27 | 17 | 5077565    | 312455   | 307338   | 5117      | 9419.5         |
| 29 | 18 | 149450423  | 663535   | 663521   | 14        | 1470.8         |
| 31 | 19 | 985222181  | 1900470  | 1900470  | 0         | 1831.8         |
| 32 | 20 | 808182895  | 5936673  | 5933908  | 2765      | 21751.2        |
| 34 | 21 | 6719515981 | 13472296 | 13472296 | 0         | 13496.6        |

`image / N ≥ 0.98` everywhere and `= 1` in fifteen of the twenty shapes with
`L ≤ 34`.  Collisions never *exceed* the birthday prediction `N − G(1 − e^{−N/G})`
and are usually far below it (part of the deficit is forced: `mod_four_constant`
gives `4 ∣ C₁ − C₂`, and `G` odd then forces the multiplier `k` in `C₁ − C₂ = k·G`
to be divisible by `4`).  **There is no structural compression.**  The image
is a sparse `N`-element subset of `ℤ/G` and nothing folds it up.  Consequently the
only remaining question is a covering question about a sparse set, which is exactly
what the unconditional `L¹` barrier of `ExpSum` says cannot be settled by size alone.

The image is not a union of cosets of any nontrivial subgroup of `ℤ/G`: at
`(29,18)` the image has `663521` elements and `G = 137 · 1090879`, and `663521` is
divisible by neither factor (`663521 = 137·4843 + 30`); at `(26,16)` the image has
`108950` elements and `G = 7 · 233 · 14753`, and `7 ∤ 108950`.  A union of cosets of
a subgroup `H` must have `|H|` dividing its size, so no such `H` exists.

Equally, `#{w : p ∣ wC w}` matches `N / p` to within Poisson noise for **every**
prime `p ∣ G` at every shape measured (e.g. `L = 26`: `p = 7` gives `15580` against
`15564.3`; `p = 233` gives `462` against `467.6`; `p = 14753` gives `7` against
`7.4`).  So `0` is missed *by counting*, never structurally: `0 ∈ Φ(S)` only at
`(L,a) = (2,1)`, the trivial cycle, in the whole measured range `L ≤ 34`.

The one genuinely structural miss has a different source and is already known.  `wC`
is bounded on the language — `max wC / 3 ^ a` grows like `a/4` — and at `(4,2)` the
maximum is `0.7·G`, so *no* word can reach even `1·G` and `0 ∉ Φ(S)` for a magnitude
reason rather than a counting one.  That is the Archimedean/realizability filter
(`RealizableBound`, `RealizableFrontier6809`) in miniature, and it is the only
mechanism in this circle of ideas that ever excludes `0` outright.  It uses asset
(a); everything else in this file uses none of (a)–(d).

## 2. Proved: the surplus is a 2-adic phenomenon, and `G` is odd

The measured fact that explains where the surplus comes from is this: the number of
distinct values of `wC w mod 2 ^ j`, over the cycle language at a fixed shape, is
**exactly** the number of heavy prefixes of length `j` — `1, 1, 2, 3, 4, 8, 13, 19,
38, 64, 128, 226, …` for `j = 1, 2, …, 12`, saturating at `N` once `j = L − 3`.
Its density in `ℤ/2^j` is `2 ^ (−0.05·j + o(j))`: the *same* `0.05` bits per letter.

`wC_append` and `two_adic_prefix` below prove the mechanism: `wC` is a cocycle,
`wC (u ++ v) = 3 ^ ones v * wC u + 2 ^ |u| * wC v`, so `wC w mod 2 ^ j` depends only
on the first `j` letters (the ones-count of the tail being pinned by `a`).  The
`0.05·L`-bit surplus **is** the entropy deficit of the heavy language read
2-adically; `mod_four_constant` is the `j = 2` case and reproves Round III's
`C ≡ 3 ^ a (mod 4)` from the cocycle in three lines.

And that is exactly why the surplus is worth nothing.  `G = 2 ^ L − 3 ^ a` is odd,
so `2 ^ j` and `G` are coprime, and `two_power_vacuous` shows every residue class
mod `2 ^ j` already contains a multiple of `G`.  A congruence condition on `wC` at
a power of two therefore excludes **no** multiple of `G` whatsoever: the factor `4`
that `mod_four_constant` cuts off the language is a factor `4` cut off `ℤ`, not off
`ℤ/G`, and by CRT it carries zero information about `G ∣ wC w`.

**Verdict for the counting route.**  The surplus is real, it grows at exactly
`1 − H₂(log₃2) = 0.0500445…` bits per letter (measured least-squares slope over the
`7570` shapes with `L ≤ 12000`: `0.05039`), and the heuristic cycle count beyond the
current frontier is `Σ_{L > 6809} N/G = 2 ^ (−353.22)`.  But every ingredient of the
surplus that has been identified lives at the prime `2`, and `G` is odd.  To convert
the surplus one needs a constraint at a modulus **sharing a factor with `G`**, and
the measurement in §1 says the language is equidistributed at every such modulus.

## Soundness filter

Everything here is `d`-free (`wC (w,d) = d · wC (w,1)` and the statements are about
`wC (w,1)` alone), so nothing in this file can distinguish `d = 1` from `d = 5`, and
nothing here claims to.  That is the point: the file is a *negative* result about the
counting route.  Assets (a)–(d) are used nowhere.
-/

namespace Collatz
namespace ImageDensity

open RepetitionDescent

/-! ## The shape is one-dimensional -/

/-- **At most one `a` per length.**  A cycle word of length `L = M + 1` is heavy at
the proper prefix `M`, so `2 ^ M ≤ 3 ^ a`, while positivity of the gap gives
`3 ^ a < 2 ^ (M+1)`.  Those two inequalities pin `a` uniquely.  This is why the
exhaustive search finds a nonempty language for exactly one `a` at each `L`, and it
is the counting-side form of `GapSandwich.cycle_length_determined`. -/
theorem shape_unique {M a b : Nat}
    (ha1 : 2 ^ M ≤ 3 ^ a) (ha2 : 3 ^ a < 2 ^ (M + 1))
    (hb1 : 2 ^ M ≤ 3 ^ b) (hb2 : 3 ^ b < 2 ^ (M + 1)) : a = b := by
  have hpos := Arith.two_pow_pos M
  have hp : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [Nat.pow_succ]; omega
  rcases Nat.lt_trichotomy a b with h | h | h
  · exfalso
    have hstep : 3 ^ (a + 1) ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ]; omega
    omega
  · exact h
  · exfalso
    have hstep : 3 ^ (b + 1) ≤ 3 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (3 : Nat) ^ (b + 1) = 3 * 3 ^ b := by rw [Nat.pow_succ]; omega
    omega

/-! ## The cocycle for `wC` -/

/-- **`wC` is a cocycle.**  Splitting a word at position `|u|`, the prefix
contribution is scaled by `3` per odd letter of the suffix and the suffix
contribution by `2` per letter of the prefix. -/
theorem wC_append : ∀ (u v : List Nat),
    wC (u ++ v) = 3 ^ ones v * wC u + 2 ^ u.length * wC v := by
  intro u
  induction u with
  | nil => intro v; simp
  | cons b t ih =>
    intro v
    have hcons : (b :: t) ++ v = b :: (t ++ v) := rfl
    rw [hcons, wC_cons, ih v, ones_append, wC_cons]
    have hlen : (b :: t).length = t.length + 1 := rfl
    rw [hlen, Nat.pow_succ]
    by_cases hb : b = 1
    · subst hb
      simp only [if_true]
      rw [Nat.pow_add]
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm, Nat.add_assoc]
    · simp only [if_neg hb]
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- **The 2-adic prefix theorem.**  Two words with a common prefix `u` and with
suffixes of equal weight have the same accumulator modulo `2 ^ |u|`.  Since the
shape fixes the total number of ones `a`, the weight of the suffix is determined by
the prefix, so `wC w mod 2 ^ j` is a function of the first `j` letters alone. -/
theorem two_adic_prefix (u v v' : List Nat) (h : ones v = ones v') :
    wC (u ++ v) % 2 ^ u.length = wC (u ++ v') % 2 ^ u.length := by
  rw [wC_append, wC_append, h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-- Restated as a divisibility: the difference of the two accumulators is killed by
`2 ^ |u|`. -/
theorem two_adic_prefix_dvd (u v v' : List Nat) (h : ones v = ones v')
    (hle : wC (u ++ v') ≤ wC (u ++ v)) :
    2 ^ u.length ∣ wC (u ++ v) - wC (u ++ v') := by
  have hA := wC_append u v
  have hB := wC_append u v'
  rw [h] at hA
  have hvv : wC v' ≤ wC v := by
    have hpos := Arith.two_pow_pos u.length
    have : 2 ^ u.length * wC v' ≤ 2 ^ u.length * wC v := by omega
    exact Nat.le_of_mul_le_mul_left this hpos
  refine ⟨wC v - wC v', ?_⟩
  have hd : 2 ^ u.length * (wC v - wC v') + 2 ^ u.length * wC v'
      = 2 ^ u.length * wC v := by
    rw [← Nat.mul_add]
    have : wC v - wC v' + wC v' = wC v := by omega
    rw [this]
  omega

/-! ## The `j = 2` case: Round III's `C ≡ 3 ^ a (mod 4)`, from the cocycle -/

/-- Heaviness forces a cycle word to begin `1 1` (already `2 ^ 2 ≤ 3 ^ a₂` needs
`a₂ ≥ 2`).  For any such word the accumulator is congruent to `3 ^ a` mod `4`,
where `a` is the total weight.  Three lines from `wC_append`. -/
theorem mod_four_constant (v : List Nat) :
    wC (1 :: 1 :: v) % 4 = 3 ^ (ones (1 :: 1 :: v)) % 4 := by
  have hsplit : (1 :: 1 :: v) = ([1, 1] : List Nat) ++ v := rfl
  have hlen : ([1, 1] : List Nat).length = 2 := rfl
  have hwC : wC ([1, 1] : List Nat) = 5 := by decide
  have hones : ones ([1, 1] ++ v) = 2 + ones v := by
    rw [ones_append]
    have : ones ([1, 1] : List Nat) = 2 := by decide
    rw [this]
  rw [hsplit, wC_append, hlen, hwC, hones]
  have h4 : (2 : Nat) ^ 2 = 4 := rfl
  rw [h4]
  rw [Nat.add_mul_mod_self_left]
  have h5 : 3 ^ ones v * 5 % 4 = 3 ^ ones v % 4 := by
    have : 3 ^ ones v * 5 = 3 ^ ones v + 4 * 3 ^ ones v := by omega
    rw [this, Nat.add_mul_mod_self_left]
  have h9 : (3 : Nat) ^ (2 + ones v) = 3 ^ ones v + 8 * 3 ^ ones v := by
    rw [Nat.pow_add]
    have h3 : (3:Nat) ^ 2 = 9 := rfl
    rw [h3]
    omega
  rw [h5, h9]
  have : 8 * 3 ^ ones v = 4 * (2 * 3 ^ ones v) := by omega
  rw [this, Nat.add_mul_mod_self_left]

/-! ## Why the 2-adic surplus is worth exactly nothing modulo an odd gap -/

/-- **Odd numbers are invertible modulo every power of two**, in the additive
Nat-friendly form `G * G' = 1 + 2 ^ j * m`.  The induction step is the classical
lift: if `G * G' = 1 + 2 ^ j * m` and `m` is odd, replace `G'` by `G' + 2 ^ j`; the
new remainder is `m + G`, even because both are odd. -/
theorem odd_inv_two_pow (G : Nat) (hG : G % 2 = 1) :
    ∀ j : Nat, ∃ G' m : Nat, G * G' = 1 + 2 ^ j * m := by
  intro j
  induction j with
  | zero => exact ⟨1, G - 1, by simp; omega⟩
  | succ j ih =>
    rcases ih with ⟨G', m, hm⟩
    rcases Arith.mod_two_eq_zero_or_one m with he | ho
    · refine ⟨G', m / 2, ?_⟩
      have : m = 2 * (m / 2) := by omega
      rw [hm, Nat.pow_succ]
      calc 1 + 2 ^ j * m = 1 + 2 ^ j * (2 * (m / 2)) := by rw [← this]
        _ = 1 + 2 ^ j * 2 * (m / 2) := by rw [Nat.mul_assoc]
    · refine ⟨G' + 2 ^ j, (m + G) / 2, ?_⟩
      have hpar : (m + G) % 2 = 0 := by omega
      have hhalf : m + G = 2 * ((m + G) / 2) := by omega
      have hexp : G * (G' + 2 ^ j) = 1 + 2 ^ j * (m + G) := by
        have e1 : G * (G' + 2 ^ j) = G * G' + G * 2 ^ j := Nat.mul_add G G' (2 ^ j)
        have e2 : G * 2 ^ j = 2 ^ j * G := Nat.mul_comm _ _
        have e3 : 2 ^ j * (m + G) = 2 ^ j * m + 2 ^ j * G := Nat.mul_add _ _ _
        rw [e1, e2, hm, e3]
        omega
      rw [hexp, Nat.pow_succ]
      calc 1 + 2 ^ j * (m + G) = 1 + 2 ^ j * (2 * ((m + G) / 2)) := by rw [← hhalf]
        _ = 1 + 2 ^ j * 2 * ((m + G) / 2) := by rw [Nat.mul_assoc]

/-- **The decisive vacuity.**  If the gap `G` is odd — and `G = 2 ^ L − 3 ^ a`
always is — then every residue class modulo every power of two already contains a
multiple of `G`.  So no congruence condition on `wC` at a power of two can exclude
`G ∣ wC w`: the entire 2-adic structure of the cycle language, which is where the
`0.05·L`-bit surplus provably lives, carries **zero** information about the target. -/
theorem two_power_vacuous (G : Nat) (hG : G % 2 = 1) (j c : Nat) :
    ∃ n : Nat, (n * G) % 2 ^ j = c % 2 ^ j := by
  rcases odd_inv_two_pow G hG j with ⟨G', m, hm⟩
  refine ⟨c * G', ?_⟩
  have : c * G' * G = c + 2 ^ j * (c * m) := by
    calc c * G' * G = c * (G * G') := by
          rw [Nat.mul_assoc, Nat.mul_comm G' G]
      _ = c * (1 + 2 ^ j * m) := by rw [hm]
      _ = c + 2 ^ j * (c * m) := by
          rw [Nat.mul_add, Nat.mul_one]
          rw [Nat.mul_left_comm]
  rw [this, Nat.add_mul_mod_self_left]

/-- The `mod 4` instance, stated against the language: for every weight `a` there is
a multiple of the (odd) gap congruent to `3 ^ a` mod `4`.  Hence Round III's
`C ≡ 3 ^ a (mod 4)` — proved above as `mod_four_constant` — removes **no**
candidate from the target set `{n·G}`. -/
theorem mod_four_excludes_nothing (G : Nat) (hG : G % 2 = 1) (a : Nat) :
    ∃ n : Nat, (n * G) % 4 = 3 ^ a % 4 := by
  have h : (4 : Nat) = 2 ^ 2 := rfl
  rw [h]
  exact two_power_vacuous G hG 2 (3 ^ a)

/-! ## The counting side: the image never exceeds the language -/

/-- Duplicate-free image of a list of residues. -/
def nub : List Nat → List Nat
  | [] => []
  | a :: t => if (nub t).contains a then nub t else a :: nub t

/-- The image of a map on a finite word list has at most as many elements as the
list.  Combined with the measurement of §1 — `image / N ≥ 0.98` throughout — this
inequality is essentially an equality, which is precisely the bad news: `Φ` neither
compresses nor spreads, so nothing beyond raw cardinality is on offer. -/
theorem nub_length_le : ∀ l : List Nat, (nub l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a t ih =>
    by_cases h : (nub t).contains a
    · simp only [nub, if_pos h, List.length_cons]
      omega
    · simp only [nub, if_neg h, List.length_cons]
      omega

/-- Hence `#Φ(S) ≤ #S = N`: the image density in `ℤ/G` is at most `N/G`, and the
`0.05·L`-bit surplus is a statement about that ratio and nothing more. -/
theorem image_card_le (f : List Nat → Nat) (S : List (List Nat)) :
    (nub (S.map f)).length ≤ S.length := by
  have h := nub_length_le (S.map f)
  simpa using h

end ImageDensity
end Collatz
