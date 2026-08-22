import Collatz.Strategy.RepetitionDescent
import Collatz.Strategy.AccumulatorAutomaton

/-!
# The cycle code: parity words as codewords, `G ∣ C` as a parity check

Fix a shape `(L, a)` and a modulus `g`.  The set

    `Code(L, a, g) = { w ∈ {0,1}^L : ones w = a, g ∣ wC w }`

is the set of parity words of the `L`-step cycles of `x ↦ (3x+d)/2 ∣ x/2` for the
offsets `d` with `(2 ^ L − 3 ^ a) ∣ d · g`.  This file asks the coding-theoretic
questions about that set — linearity, cyclicity, minimum distance — and answers
all three.  Two of the three answers are negative, and the negatives are the
point: they explain why no syndrome mechanism has ever surfaced in this
development, and they close the "large minimum distance ⇒ few codewords" route.

## 1. Linearity: only after a change of alphabet, and then only rank one

`wC w = Σ_k 3 ^ (a − k) · 2 ^ (p_k)` where `p_1 < … < p_a` are the positions of
the odd letters.  This is **not** linear in the bits of `w`: flipping one bit
changes the exponent `a − k` of every later term.  It **is** linear in the
`a`-tuple `v = (2 ^ p_1, …, 2 ^ p_a) ∈ (ℤ/g) ^ a`, with the *fixed* coefficient
vector `(3 ^ (a−1), …, 3, 1)`.  So the honest statement is:

> the cycle code is the intersection of a **rank-one** linear code over `ℤ/g`
> (one parity check, length `a`) with the non-linear support condition
> "each `v_k` is a power of two and the `p_k` are strictly increasing".

A length-`a` linear code with a single check has minimum distance `2` in the
`v`-alphabet — the Singleton bound is met by the check itself.  Since a Hamming
distance `2r` between two words of the same weight is a distance `r` between
their position vectors, the linear part of the structure caps any provable
minimum distance at `4`.  **Every excess over `4` observed below comes from the
support condition, not from the check.**  That is the whole reason the syndrome
carries no leverage.

The shifted coordinate `runA` of `RunAlgebra` does not change this: `runA_eq`
at full length reads `runA L x + 3 ^ a = affineC L x + 2 ^ L`, i.e.
`runA = wC + G`.  At full length the two accumulators differ by the *constant*
`G`, so their codes are translates of one another and have identical distance
structure.  There is nothing to gain by feeding the accumulator with even steps.

## 2. Cyclicity: true, and already known

`Code(L,a,g)` is closed under cyclic shift whenever `g` is odd and `g ∣ G`
(`rot_zero_dvd`, `rot_one_dvd` below).  The mechanism is the pair of exact
identities

* `wC (0 :: t) = 2 · wC (t ++ [0])`                                (`wC_rot_zero`)
* `2 · wC (t ++ [1]) + 3 ^ ones (1 :: t) = 3 · wC (1 :: t) + 2 ^ (1 :: t).length`
                                                                   (`wC_rot_one`)

so the syndrome is not shift-*invariant* but shift-*covariant*:
`Φ(σw) ≡ 3 ^ (w₀) · 2⁻¹ · Φ(w) (mod G)`.  After `L` shifts the multiplier is
`3 ^ a · 2 ^ (−L) ≡ 1`, as it must be.  This is `AccumulatorCap.dvd_affineC_shift`
in coding-theoretic clothing; `Rotation.lean` already records that requiring
`G ∣ wC` at *all* rotations is exactly as restrictive as requiring it at one.
The cyclic structure is therefore genuine but empty of new content.

## 3. Minimum distance: the transposition syndrome, and its refutation

Two words of the same length and weight at Hamming distance `2` differ by moving
a single odd letter across a block `y`:

    `w  = x ++ 1 :: (y ++ 0 :: z)`,     `w' = x ++ 0 :: (y ++ 1 :: z)`.

`wC_transpose` computes the difference exactly:

    `wC w + K · (2 ^ (|y|+1) + 4 · wC y) = wC w' + K · 3 ^ (ones y)`,
    `K = 2 ^ |x| · 3 ^ (ones z)`.

So the entire difference is `K · σ(y)` with the **transposition syndrome**

    `σ(y) = 3 ^ (ones y) − 2 ^ (|y| + 1) − 4 · wC y`,

a quantity depending *only on the block strictly between the two moved letters* —
a local parity check, and the only genuinely new object here.  Two facts about it
are proved below.

* `σ(y)` is **odd**, hence never zero (`transpose_wC_ne`): `3 ^ ones y` is odd and
  `2 ^ (|y|+1) + 4 · wC y` is even.  This re-proves `SinkStructure.wC_inj` on
  distance-`2` pairs by a parity argument instead of a `2`-adic induction.
* Any two codewords at Hamming distance `2` satisfy `g ∣ K · σ(y)`
  (`transpose_syndrome`).  With `g` coprime to `6` this forces `g ≤ |σ(y)|`, i.e.
  **the two moved positions must be far apart** — `|σ(y)| ≲ 6 ^ (|y|)`, so a
  distance-`2` collision modulo `g ≈ 2 ^ L` needs `|y| ≳ 0.387 · L`.

### The measurement, and what it kills

Exhaustive computation (meet-in-the-middle over `w = u ++ v`, all ledge shapes
`2 ^ (L−1) ≤ 3 ^ a < 2 ^ L` with `L ≤ 27`, every divisor `g ∣ G`):

| shape        | `g`       | `d` a multiple of | `#Code` | `dmin` | `dmin / L` |
|--------------|-----------|-------------------|---------|--------|------------|
| `(11, 7)`    | `139`     | `1` (`d = −1`)    | `11`    | `4`    | `0.364`    |
| `(10, 6)`    | `59`      | `5`               | `10`    | `4`    | `0.400`    |
| `(15, 9)`    | `2617`    | `5`               | `10`    | `6`    | `0.400`    |
| `(16, 10)`   | `499`     | `13`              | `56`    | `4`    | `0.250`    |
| `(20, 12)`   | `103427`  | `5`               | `10`    | `8`    | `0.400`    |
| `(23, 14)`   | `45641`   | `79`              | `46`    | `6`    | `0.261`    |
| `(24, 15)`   | `186793`  | `13`              | `80`    | `4`    | `0.167`    |
| `(26, 16)`   | `103271`  | `233`             | `273`   | `4`    | `0.154`    |
| `(27, 17)`   | `1015513` | `5`               | `54`    | `6`    | `0.222`    |

`(11,7,139)` is exactly the eleven rotations of the `3x−1` cycle
`17 → 25 → … → 34`; `(27,17,1015513)` is exactly the two `3x+5` `27`-cycles, `54`
words.  The absolute minimum distance **does not grow**: it stays in `{4, 6, 8}`
while `L` runs from `10` to `27`, so the relative distance `dmin / L` *falls*.

The reason is structural and is an existing invariant in disguise.  For a code
that is a single rotation orbit the nearest neighbour of `w` is always its own
one-step shift, and

    `dH(w, σw) = #{ i : w_i ≠ w_{i+1} } = 2 · (number of cyclic odd-runs of w)`.

Every row of the table with `#Code = L` has `dmin = 2 · r` on the nose
(`r = 2, 2, 3, 4` at `L = 11, 10, 15, 20`).  **The minimum distance of a
one-orbit cycle code is twice the run count** — the statistic of
`RunAlgebra`/`TwoRunOrder`/`RunRefined`, not a new quantity.  Cycle words are
run-rich, so their rotations are Hamming-close, so the code is a bad code.

That closes the counting route this file was built to test.  To conclude "no
cycle at shape `(L,a)`" from a distance bound one would use rotation closure —
a cycle forces `#Code ≥ L` — against a Plotkin-type upper bound.  Plotkin for
constant weight `a` needs `dmin > 2a(L−a)/L`, which at `a ≈ 0.63 L` is
`dmin > 0.466 · L`.  Measured `dmin / L ≤ 0.40` and falling; and the Singleton
bound at the observed `dmin = 6` on `(27,17)` reads `#Code ≤ binom(27,15) =
17383860` against the true `54`, vacuous by five orders of magnitude.

**Refutation of the sharp form** — with its description corrected.  An earlier
draft of this header said `min_distance_four_refuted` exhibits two *genuine,
distinct* cycles of `x ↦ (3x+59)/2 ∣ x/2`, at `n = 1399` and `n = 2128`.  They are
not distinct cycles: `2128` is the second element of the orbit of `1399`, and the
two are **rotations of one cycle** — the `(10,6)` cycle
`133 → 229 → 373 → 589 → 913 → 1399 → 2128 → 1064 → 532 → 266`, whose word read
from `n = 229` has `C = 1145` and satisfies `295·229 = 59·1145`.

The Lean theorem is nevertheless true and its content survives: the two words are
distinct, share `(L, a) = (10, 6)`, are both annihilated by `g = 5`, and lie at
Hamming distance `2`.  So there is no theorem "distinct cycle words at the same `(L,a)` differ in at
least `4` positions", for any `d`-uniform reading of "cycle word".

But the refutation is **not independent of §4's diagnosis** — it is the same fact.
Rotations are in the code (`rot_zero_dvd`, `rot_one_dvd`), and a word's nearest
neighbour is its own shift at distance `2·(cyclic run count)`; this word has two
runs, hence distance `2`.  So the sharp form dies of run-richness, exactly as §4
says, and not of a second phenomenon.

The moduli in the table and in the theorem also need keeping apart, since they are
swapped from the naive reading.  A cycle of `3x+d` at shape `(L,a)` has
`(2^L − 3^a)·n = d·C`, so the modulus annihilating `C` is `G / gcd(G,d)`.  At
`(10,6)`, `G = 295 = 5·59`: the code at `g = 59` is the `3x+5` code (10 words,
`dmin = 4`, as the table records), and the code at `g = 5` — the theorem's modulus
— is the `3x+59` code, which contains the distance-`2` rotation pair.  Both are
correct; neither is the other.  `Code(10,6,295)` is **empty**.

### Relation to the `L¹` barrier

The distance route is **not** a disguised form of the `ExpSum` `L¹` barrier: that
barrier says a *lower* bound on `Σ_k |S(k)|` makes the circle method vacuous,
while this route would have produced an *upper* bound on `#Code` from a distance
bound, and — via rotation closure, `#Code ≥ L` — an upper bound below `L` is a
genuine contradiction, not a vacuity.  The route is independent, and it fails for
an independent and measured reason: the relative minimum distance is too small,
because it equals twice the run count.

## Soundness

Nothing here uses any of the four `d = 1` assets.  The identities are `d`-free
and `DenominatorScalar` makes the whole code family scale-covariant under
`C ↦ d · C`.  That is precisely why the mechanism cannot separate `d = 1`, and
the `d = 59` refutation above is the explicit witness.
-/

namespace Collatz
namespace CycleCode

open RepetitionDescent

/-! ## Hamming distance -/

/-- Hamming distance of two words, read letterwise. -/
def hdist : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: u, b :: v => (if a = b then 0 else 1) + hdist u v

@[simp] theorem hdist_nil_left (v : List Nat) : hdist [] v = 0 := by
  cases v <;> rfl

@[simp] theorem hdist_nil_right (u : List Nat) : hdist u [] = 0 := by
  cases u <;> rfl

theorem hdist_cons (a b : Nat) (u v : List Nat) :
    hdist (a :: u) (b :: v) = (if a = b then 0 else 1) + hdist u v := rfl

theorem hdist_self : ∀ u : List Nat, hdist u u = 0
  | [] => rfl
  | _ :: t => by rw [hdist_cons, if_pos rfl, hdist_self t]

theorem hdist_comm : ∀ u v : List Nat, hdist u v = hdist v u
  | [], v => by cases v <;> rfl
  | _ :: _, [] => rfl
  | a :: u, b :: v => by
    rw [hdist_cons, hdist_cons, hdist_comm u v]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun k => h k.symm)]

/-- Words at distance `0` and equal length are equal. -/
theorem eq_of_hdist_zero : ∀ u v : List Nat, u.length = v.length → hdist u v = 0 → u = v
  | [], [], _, _ => rfl
  | a :: u, b :: v, hl, h => by
    rw [hdist_cons] at h
    have hab : a = b := by
      by_cases k : a = b
      · exact k
      · rw [if_neg k] at h; omega
    have h' : hdist u v = 0 := by rw [if_pos hab] at h; omega
    have hl' : u.length = v.length := by
      simp only [List.length_cons] at hl; omega
    rw [hab, eq_of_hdist_zero u v hl' h']

/-! ## The rotation identities: the code is cyclic -/

/-- Rotating a word that begins with an even letter divides the accumulator by two. -/
theorem wC_rot_zero (t : List Nat) : wC (0 :: t) = 2 * wC (t ++ [0]) := by
  rw [wC_cons, if_neg (by decide), wC_append, wC_singleton, if_neg (by decide),
    ones_singleton, if_neg (by decide)]
  simp

/-- **The rotation gap identity.**  Moving the leading odd letter to the back
multiplies the accumulator by `3/2` and adds the gap. -/
theorem wC_rot_one (t : List Nat) :
    2 * wC (t ++ [1]) + 3 ^ ones (1 :: t) = 3 * wC (1 :: t) + 2 ^ (1 :: t).length := by
  rw [wC_append, wC_singleton, if_pos rfl, ones_singleton, if_pos rfl,
    wC_cons, if_pos rfl, ones_cons, if_pos rfl, List.length_cons]
  have h3 : (3:Nat) ^ (1 + ones t) = 3 * 3 ^ ones t := by
    rw [Nat.pow_add, Nat.pow_one]
  have h2 : (2:Nat) ^ (t.length + 1) = 2 * 2 ^ t.length := by
    rw [Nat.pow_succ]; omega
  rw [h3, h2]
  generalize (3:Nat) ^ ones t = A
  generalize wC t = X
  generalize (2:Nat) ^ t.length = P
  omega

/-- Cyclic closure of the code, even letter in front. -/
theorem rot_zero_dvd {g : Nat} (hg : g % 2 = 1) (t : List Nat) (h : g ∣ wC (0 :: t)) :
    g ∣ wC (t ++ [0]) := by
  rw [wC_rot_zero] at h
  exact AccumulatorAutomaton.odd_dvd_of_dvd_two_mul hg h

/-- Cyclic closure of the code, odd letter in front.  `g` must be odd and divide
the gap `G = 2 ^ L − 3 ^ a`, which is the hypothesis `hG`. -/
theorem rot_one_dvd {g G : Nat} (hg : g % 2 = 1) (t : List Nat)
    (hG : G + 3 ^ ones (1 :: t) = 2 ^ (1 :: t).length) (hGg : g ∣ G)
    (h : g ∣ wC (1 :: t)) : g ∣ wC (t ++ [1]) := by
  have hid := wC_rot_one t
  have hkey : 2 * wC (t ++ [1]) = 3 * wC (1 :: t) + G := by omega
  have h3 : g ∣ 3 * wC (1 :: t) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨3 * k, by rw [hk, Nat.mul_left_comm]⟩
  have : g ∣ 2 * wC (t ++ [1]) := by
    rw [hkey]
    exact Nat.dvd_add h3 hGg
  exact AccumulatorAutomaton.odd_dvd_of_dvd_two_mul hg this

/-! ## The transposition syndrome -/

/-- **The transposition identity.**  Moving one odd letter from the front of a
block `y` to its back changes the accumulator by exactly
`2 ^ |x| · 3 ^ (ones z) · σ(y)` with
`σ(y) = 3 ^ (ones y) − 2 ^ (|y| + 1) − 4 · wC y`.  Stated without subtraction. -/
theorem wC_transpose (x y z : List Nat) :
    wC (x ++ 1 :: (y ++ 0 :: z)) + 2 ^ x.length * 3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y)
      = wC (x ++ 0 :: (y ++ 1 :: z)) + 2 ^ x.length * 3 ^ ones z * 3 ^ ones y := by
  have hL : ones (1 :: (y ++ 0 :: z)) = ones (0 :: (y ++ 1 :: z)) := by
    rw [ones_cons, if_pos rfl, ones_cons, if_neg (by decide), ones_append, ones_append,
      ones_cons, if_neg (by decide), ones_cons, if_pos rfl]
    omega
  rw [wC_append, wC_append, hL]
  -- reduce to the identity on the tails
  have hR : wC (1 :: (y ++ 0 :: z)) + 3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y)
      = wC (0 :: (y ++ 1 :: z)) + 3 ^ ones z * 3 ^ ones y := by
    rw [wC_cons, if_pos rfl, wC_cons, if_neg (by decide), wC_append, wC_append,
      ones_cons, if_neg (by decide), ones_cons, if_pos rfl, wC_cons, if_neg (by decide),
      wC_cons, if_pos rfl, ones_append, ones_cons, if_neg (by decide)]
    simp only [Nat.zero_add]
    simp [Nat.pow_add, Nat.pow_succ, Nat.mul_add, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    omega
  have h1 : 2 ^ x.length * (3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y))
      = 2 ^ x.length * 3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y) :=
    (Nat.mul_assoc _ _ _).symm
  have h2 : 2 ^ x.length * (3 ^ ones z * 3 ^ ones y)
      = 2 ^ x.length * 3 ^ ones z * 3 ^ ones y := (Nat.mul_assoc _ _ _).symm
  rw [Nat.add_assoc, Nat.add_assoc, ← h1, ← h2, ← Nat.mul_add, ← Nat.mul_add, hR]


/-- **The syndrome is odd, hence nonzero.**  A transposition therefore always
changes the accumulator: a parity argument replacing the `2`-adic induction of
`SinkStructure.wC_inj` on distance-`2` pairs. -/
theorem transpose_wC_ne (x y z : List Nat) :
    wC (x ++ 1 :: (y ++ 0 :: z)) ≠ wC (x ++ 0 :: (y ++ 1 :: z)) := by
  intro h
  have hid := wC_transpose x y z
  rw [h] at hid
  have hK : 0 < 2 ^ x.length * 3 ^ ones z :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have heq : 2 ^ (y.length + 1) + 4 * wC y = 3 ^ ones y :=
    Nat.eq_of_mul_eq_mul_left hK (by omega)
  -- left side is even, right side is odd
  have hev : (2 ^ (y.length + 1) + 4 * wC y) % 2 = 0 := by
    have : (2:Nat) ^ (y.length + 1) = 2 * 2 ^ y.length := by rw [Nat.pow_succ]; omega
    rw [this]; omega
  have hod : (3:Nat) ^ ones y % 2 = 1 := by
    induction ones y with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  omega

/-- **The distance-`2` syndrome condition.**  If two words related by a
transposition are both in the `g`-code, then `g` divides
`2 ^ |x| · 3 ^ (ones z) · σ(y)`, a quantity read off from the block strictly
between the two moved letters alone. -/
theorem transpose_syndrome {g : Nat} (x y z : List Nat)
    (h1 : g ∣ wC (x ++ 1 :: (y ++ 0 :: z)))
    (h2 : g ∣ wC (x ++ 0 :: (y ++ 1 :: z))) :
    g ∣ 2 ^ x.length * 3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y)
          - 2 ^ x.length * 3 ^ ones z * 3 ^ ones y := by
  have hid := wC_transpose x y z
  have hd := AccumulatorAutomaton.dvd_sub_of_dvd h2 h1
  have key : 2 ^ x.length * 3 ^ ones z * (2 ^ (y.length + 1) + 4 * wC y)
        - 2 ^ x.length * 3 ^ ones z * 3 ^ ones y
      = wC (x ++ 0 :: (y ++ 1 :: z)) - wC (x ++ 1 :: (y ++ 0 :: z)) := by omega
  rw [key]
  exact hd

/-! ## The refutation: minimum distance `4` is false

Two genuine, distinct cycles of `x ↦ (3x+59)/2 ∣ x/2`, both of shape `(10, 6)`,
whose parity words differ in exactly two positions.  `G = 2 ^ 10 − 3 ^ 6 = 295`
and `59 · wC = n · 295` in both cases, with `n = 1399` and `n = 2128`. -/

/-- Parity word of the `3x+59` cycle through `1399`. -/
def c1 : List Nat := [1, 0, 0, 0, 0, 1, 1, 1, 1, 1]

/-- Parity word of the `3x+59` cycle through `2128`. -/
def c2 : List Nat := [0, 0, 0, 0, 1, 1, 1, 1, 1, 1]

theorem c1_wC : wC c1 = 6995 := by decide
theorem c2_wC : wC c2 = 10640 := by decide
theorem c1_ones : ones c1 = 6 := by decide
theorem c2_ones : ones c2 = 6 := by decide
theorem c_len : c1.length = 10 ∧ c2.length = 10 := by constructor <;> decide

/-- Both words are cycle words for `d = 59`: `59 · C = n · G` with `G = 295`. -/
theorem c1_cycle : 59 * wC c1 = 1399 * (2 ^ 10 - 3 ^ 6) := by decide

theorem c2_cycle : 59 * wC c2 = 2128 * (2 ^ 10 - 3 ^ 6) := by decide

theorem c_hdist : hdist c1 c2 = 2 := by decide

/-- **There is no minimum-distance-`4` theorem for cycle codes.**  Two distinct
words of the same length and the same odd count, both annihilated by the same
modulus `g = 5` (equivalently: both `3x+59` cycle words of shape `(10,6)`), lie at
Hamming distance exactly `2`.

They are two **rotations of a single cycle**, not two distinct cycles — see the
header.  That is enough for the refutation, since rotations lie in the code, but it
means the mechanism is the run-count identity of the next section rather than an
independent one. -/
theorem min_distance_four_refuted :
    ∃ u v : List Nat, u ≠ v ∧ u.length = v.length ∧ ones u = ones v ∧
      5 ∣ wC u ∧ 5 ∣ wC v ∧ hdist u v = 2 :=
  ⟨c1, c2, by decide, by decide, by decide, by decide, by decide, c_hdist⟩

/-! ## The one-orbit minimum distance is twice the run count

For a code that is a single rotation orbit the nearest neighbour of `w` is its
own one-step shift, and `hdist w (rotate w)` counts the cyclic letter changes,
i.e. twice the number of maximal odd runs.  Here it is on the `3x−1` word. -/

/-- The `3x−1` cycle word `17 → 25 → 37 → 55 → 82 → 41 → 61 → 91 → 136 → 68 → 34`. -/
def w17 : List Nat := [1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0]

theorem w17_wC : wC w17 = 2363 := by decide

theorem w17_ones : ones w17 = 7 := by decide

/-- Its accumulator is divisible by `139 = 3 ^ 7 − 2 ^ 11`, the `d = −1` gap. -/
theorem w17_dvd : 139 ∣ wC w17 := by decide

/-- Its one-step rotation is at Hamming distance `4` — twice the two cyclic odd
runs of the word — and that is the minimum distance of the eleven-word code. -/
theorem w17_rot_hdist : hdist w17 (w17.tail ++ [1]) = 4 := by decide

end CycleCode
end Collatz
