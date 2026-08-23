import Collatz.Strategy.AccumulatorAutomaton

/-!
# The rotation law for the accumulator, and what it does (and does not) do to `gcd(C, G)`

Round XIV, sections 5/6/19/20/27/28/31/42/62/66/67.

## 0. The headline target is not attempted

The brief's headline, `δ(w) = G / gcd(C, G) > 1` for every non-trivial word, is
`G ∤ C`, which is the cycle half of Collatz verbatim (`CLOSURE.md`, Round IV).
Nothing below attempts it.  What is proved here is an **exact identity** and two
**closed classes**.

## 1. The identity: rotation acts on `C` by the `3x + G` map

Write `rot (b :: v) = v ++ [b]` — the cyclic left shift.  Then, with
`L = |w|` and `a = oddCount w`:

* `C_rot_false` : `C w = 2 * C (rot w)`                       (head even)
* `C_rot_true`  : `2 * C (rot w) + 3 ^ a = 3 * C w + 2 ^ L`   (head odd)

and, once the gap is positive, `C_rot_true_gap` reads the second as

    2 * C (rot w) = 3 * C w + G,        G = 2 ^ L − 3 ^ a.

So **the cyclic shift of the word is exactly one step of `x ↦ (3x + G)/2`
applied to the accumulator**, `x ↦ x/2` on an even letter.  `C` is therefore a
point of a genuine `3x + G` cycle whose parity word is `w` itself.  This is the
integral lift of the familiar statement that the orbit values of a cycle are the
accumulators of the rotations of its word; it is stated here on *arbitrary*
words, with no cycle hypothesis and no minimum.

## 2. The consequence: `gcd(C, G)` is a rotation invariant

`gcd_rot` : `gcd (C (rot w)) (gap w) = gcd (C w) (gap w)`, hence `delta_rot` :
`delta (rot w) = delta w`.  Both letters are handled by the same two
cancellations: `G` is odd, so a common divisor absorbs the factor `2`; `3 ∤ G`,
so it absorbs the factor `3`.  In particular `G ∣ C w ↔ G ∣ C (rot w)`
(`gap_dvd_C_rot_iff`) — the cycle condition is a property of the *necklace*, not
of the word.

This is exact and unconditional, and it is the strongest gcd statement this
round found.  What it is **not**: a bound.  It says the `L` rotations of a word
all carry the same `gcd`; it says nothing about how large that common value is.
Measured (`δ`-spectrum reconfirmed): over 578 random heavy words with
`20 ≤ L ≤ 60`, `gcd(C, G) = 1` in 89.3 %, the largest value seen being `247`.

## 3. Two classes closed outright

* `oddCount_one_no_cycle` : a word with exactly one odd letter and `2 < gap w`
  never satisfies `gap w ∣ C w`.  Reason: `C w = 2 ^ t` exactly
  (`C_eq_two_pow_of_oddCount_one`) and `G` is odd.
* `two_odd_closed` : for `5 ≤ L`, no pair of odd-letter positions
  `t₀ < t₁ < L` has `2 ^ L − 9 ∣ 3 * 2 ^ t₀ + 2 ^ t₁`.  Reason: the accumulator
  of a two-odd-letter word is at most `5 * 2 ^ (L−2) < 2 * G`, so `G ∣ C` forces
  `C = G`; `G` odd forces `t₀ = 0`; and then `2 ^ t₁ = 2 ^ L − 12` is impossible
  above `L = 4`.

At `L = 4` the two survivors are `t = (0,2)` and `t = (1,3)`, i.e. the words
`1010` and `0101` — the trivial cycle traversed twice.  Exhaustively (exact
integers): the *only* solutions of `G ∣ C` with `a ≤ 4` are the doubled,
tripled, quadrupled trivial word at `L = 2a`; checked for every word with
`a = 1, L < 80`; `a = 2, L < 80`; `a = 3, L < 64`; `a = 4, L < 38`.

Honest weight: a cycle has `a / L ≈ log 3 2`, so `a ≤ 4` was already out of
range.  These are warm-ups that fix the *method* — bound `C / G` by `(3/2)^a`,
then solve a finite `2`-adic equation — not new frontier.  The method has a hard
ceiling: `C ≤ 2 ^ (L−a) (3 ^ a − 2 ^ a)` gives `C / G < (3/2) ^ a`, so the number
of quotients to eliminate grows like `(3/2) ^ a` and the case split explodes.

## 4. Four routes measured and closed, with the diagnosis in each case

*(All figures exact-integer; ranges stated.  None of this enters a proof.)*

**(a) `gcd(C, G) ∣ F(L, a)` for an explicit `F` — dead.**  Over all words of
shape `(L, a)`, `L ≤ 20`, the lcm of the realised values of `gcd(C, G)` is `G`
itself at `(4,2), (10,6), (15,9), (16,10), (20,12)`.  Any true divisor relation
`gcd ∣ F(L,a)` therefore forces `G ∣ F`, i.e. says nothing.  Restricting to
heavy words leaves a smaller lcm only because heavy words are too few to sample
every divisor — the sample-size effect `DeltaSpectrum` already isolated.

**(b) Valuations, `v_p(C) < v_p(G)` — empty, and for a structural reason.**
Over 30 000 random heavy words with `8 ≤ L ≤ 34`, taking every prime
`p ∣ gcd(C, G)`: 515 observations, and `v_p(G) = 1` in **all** of them
(distribution of `v_p(C)`: 448 ones, 59 twos, 6 threes, 1 four, 1 five).  So
`v_p(C) < v_p(G)` never happened; whenever `p` divides both it divides `C` to at
least the multiplicity it divides `G`.  Diagnosis: `G` is essentially squarefree
at the primes that matter (`p ^ 2 ∣ G` for only 46 of the 1238 prime divisors of
gaps with `G < 2 ^ 40`, and never for a `p` that also divided `C`), so
"`v_p(C) < v_p(G)`" *is* "`p ∤ C`" — the valuation refinement of section 20
carries exactly zero information beyond the divisibility question it refines.

**(c) `lpf(G)` as a canonical prime — dead, it is not canonical.**  On the
Beatty corner family (`L = ⌊a log₂ 3⌋ + 1`, `C = Bcap a`, `2 ≤ a ≤ 400`, `lpf`
resolved by trial division below `2·10^5` for 346 of them): `lpf(G) ∣ C` in
**40** cases, `11.6 %`, against the chance prediction `Σ 1/lpf = 34.2`, `9.9 %`.
On 578 random heavy words with `20 ≤ L ≤ 60`: `8.82 %` observed against `9.94 %`
predicted.  `lpf(G)` divides `C` at exactly the rate a random residue would, so
`lpf(G) ∤ C` is **false** as a universal statement and no proof of it exists.
A proof would have covered about `88 %` of the extremal family — and nothing
identifies which `88 %`.

Baseline reconfirmed on the corner family: `bits(gcd(C, G))` is `1,1,1,1,1,4,1,3`
at `a = 4,7,10,17,25,50,100,300` against `bits(G) = 6,11,13,23,38,79,158,475`
(the two nontrivial gcds are `13` at `a = 50` and `5` at `a = 300`).

**(d) Primitive prime divisors — what is actually true, and Zsigmondy.**
`2 ^ L − 3 ^ a` is `X ^ d − Y ^ d` with `X = 2 ^ (L/d)`, `Y = 3 ^ (a/d)` **only**
for `d ∣ gcd(L, a)`, so Zsigmondy's theorem applies to it only through
`d = gcd(L, a)`, and is vacuous when that is `1`.  Measured: among `(L, a)`
within `0.5 %` of the Collatz ratio with `L < 400`, `gcd(L, a) = 1` for `61.8 %`.
So Zsigmondy is unavailable on the majority of the relevant shapes and **must
not be invoked** for `2 ^ L − 3 ^ a` in general.  What *is* unconditionally true
about any prime `p ∣ 2 ^ L − 3 ^ a` (`p ≥ 5` by `GapPrimes.gap_divisor_ge_five`),
with `e = ord_p 2` and `f = ord_p 3`:

* `2 ^ L ≡ 3 ^ a (mod p)`, so raising to the `f`-th and `e`-th powers,
  `e ∣ L · f` and `f ∣ a · e`;
* equal orders of the two sides: `e / gcd(e, L) = f / gcd(f, a)`;
* hence `3 ^ a ∈ ⟨2⟩ ⊆ F_p^*`, and the lattice
  `Λ = {(u,v) : 2 ^ u 3 ^ v ≡ 1}` contains `(L, −a)` alongside `(e,0)` and
  `(0,f)`, so `|⟨2,3⟩| = [Z² : Λ]` divides `[Z² : ⟨(e,0),(0,f),(L,−a)⟩]`.

Verified with zero violations on all 1006 triples `(L, a, p)` with `L < 40`,
`G < 2 ^ 40`, `p < 60000`.  The finiteness one *would* want in place of
Zsigmondy — that the prime factors of `2 ^ L − 3 ^ a` cannot all stay inside a
fixed finite set `S` — is a theorem, but a Baker/S-unit theorem, ineffective in
practice at these sizes and far outside this development's toolkit.

## 5. The one positive measurement not yet explained

For `123` of the `739` triples `(L, a, p)` with `L ≤ 34`, `p ∣ G`, `p < 30000`,
the prime `p` divides `C(w)` for **no** word of shape `(L, a)` — against `63.7`
expected if `C mod p` were uniform.  `27` of those have null probability below
`1 %`.  The `a = 1` and `a = 2` families explain part of the excess exactly: for
`a = 2`, `C = 2 ^ t₀ (2 ^ m + 3)`, so `p ∣ C` for some word iff `−3 ∈ ⟨2⟩` in
`F_p^*` **and** its discrete logarithm is at most `L − 1`.  That criterion
predicts the blocked/not-blocked status of all `62` recorded `a = 2` triples
with zero mismatches (e.g. `p = 17`: `−3 ≡ 14` is not a power of `2` mod `17`,
so `17` divides no two-odd-letter accumulator at any length).  The residual
excess at `a ≥ 3` is unexplained and is the one live thread this round leaves.
-/

namespace Collatz
namespace GapRotation

open DeltaSpectrum AccumulatorAutomaton

/-! ## 1. Two accumulator normalisations -/

/-- The accumulator is affine in its seed, with slope `3 ^ (odd count)`. -/
theorem accC_shift : ∀ (w : List Bool) (j c : Nat),
    accC w j c = 3 ^ oddCount w * c + accC w j 0 := by
  intro w
  induction w with
  | nil => intro j c; simp [accC, oddCount]
  | cons b w ih =>
    intro j c
    show accC w (j + 1) (if b then 3 * c + 2 ^ j else c)
        = 3 ^ ((if b then 1 else 0) + oddCount w) * c
          + accC w (j + 1) (if b then 3 * 0 + 2 ^ j else 0)
    cases b with
    | false =>
      show accC w (j + 1) c = 3 ^ (0 + oddCount w) * c + accC w (j + 1) 0
      rw [ih (j + 1) c, Nat.zero_add]
    | true =>
      show accC w (j + 1) (3 * c + 2 ^ j)
          = 3 ^ (1 + oddCount w) * c + accC w (j + 1) (3 * 0 + 2 ^ j)
      rw [ih (j + 1) (3 * c + 2 ^ j), ih (j + 1) (3 * 0 + 2 ^ j)]
      have h3 : (3:Nat) ^ (1 + oddCount w) = 3 * 3 ^ oddCount w := by
        rw [Nat.pow_add, Nat.pow_one]
      rw [h3]
      have : (3:Nat) * 0 + 2 ^ j = 2 ^ j := by omega
      rw [this]
      have hd : 3 ^ oddCount w * (3 * c + 2 ^ j)
          = 3 * 3 ^ oddCount w * c + 3 ^ oddCount w * 2 ^ j := by
        rw [Nat.mul_add]
        have : 3 ^ oddCount w * (3 * c) = 3 * 3 ^ oddCount w * c := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ oddCount w) 3]
        rw [this]
      rw [hd]
      omega

/-- Shifting the clock by one doubles the accumulator. -/
theorem accC_succ : ∀ (w : List Bool) (j : Nat),
    accC w (j + 1) 0 = 2 * accC w j 0 := by
  intro w
  induction w with
  | nil => intro j; simp [accC]
  | cons b w ih =>
    intro j
    show accC w (j + 1 + 1) (if b then 3 * 0 + 2 ^ (j + 1) else 0)
        = 2 * accC w (j + 1) (if b then 3 * 0 + 2 ^ j else 0)
    cases b with
    | false =>
      show accC w (j + 1 + 1) 0 = 2 * accC w (j + 1) 0
      exact ih (j + 1)
    | true =>
      show accC w (j + 1 + 1) (3 * 0 + 2 ^ (j + 1))
          = 2 * accC w (j + 1) (3 * 0 + 2 ^ j)
      have e1 : (3:Nat) * 0 + 2 ^ (j + 1) = 2 * 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      have e2 : (3:Nat) * 0 + 2 ^ j = 2 ^ j := by omega
      rw [e1, e2, accC_shift w (j + 1 + 1) (2 * 2 ^ j),
          accC_shift w (j + 1) (2 ^ j), ih (j + 1)]
      have : 3 ^ oddCount w * (2 * 2 ^ j) = 2 * (3 ^ oddCount w * 2 ^ j) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (3 ^ oddCount w) 2]
      omega

/-- **The head transition law**, dual to `C_snoc`. -/
theorem C_cons (b : Bool) (v : List Bool) :
    C (b :: v) = (if b then 3 ^ oddCount v else 0) + 2 * C v := by
  show accC v (0 + 1) (if b then 3 * 0 + 2 ^ 0 else 0) = _
  cases b with
  | false =>
    show accC v (0 + 1) 0 = 0 + 2 * accC v 0 0
    rw [accC_succ v 0]; omega
  | true =>
    show accC v (0 + 1) (3 * 0 + 2 ^ 0) = 3 ^ oddCount v + 2 * C v
    have e : (3:Nat) * 0 + 2 ^ 0 = 1 := by omega
    rw [e, accC_shift v (0 + 1) 1, accC_succ v 0]
    show 3 ^ oddCount v * 1 + 2 * accC v 0 0 = 3 ^ oddCount v + 2 * accC v 0 0
    omega

/-- No odd letters means no accumulator. -/
theorem C_eq_zero_of_oddCount_zero : ∀ {w : List Bool}, oddCount w = 0 → C w = 0 := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons b v ih =>
    intro h
    have hb : b = false := by
      cases b with
      | false => rfl
      | true => simp [oddCount] at h
    subst hb
    have hv : oddCount v = 0 := by simpa [oddCount] using h
    rw [C_cons false v, ih hv]; rfl

/-! ## 2. The cyclic shift -/

/-- Cyclic left shift of a word. -/
def rot : List Bool → List Bool
  | [] => []
  | b :: v => v ++ [b]

theorem rot_length (w : List Bool) : (rot w).length = w.length := by
  cases w with
  | nil => rfl
  | cons b v => show (v ++ [b]).length = v.length + 1; simp

theorem rot_oddCount (w : List Bool) : oddCount (rot w) = oddCount w := by
  cases w with
  | nil => rfl
  | cons b v =>
    show oddCount (v ++ [b]) = (if b then 1 else 0) + oddCount v
    rw [oddCount_snoc]; omega

/-- The gap is a rotation invariant, because both of its inputs are. -/
theorem gap_rot (w : List Bool) : gap (rot w) = gap w := by
  show 2 ^ (rot w).length - 3 ^ oddCount (rot w) = 2 ^ w.length - 3 ^ oddCount w
  rw [rot_length, rot_oddCount]

/-- **Even head: rotation halves the accumulator.** -/
theorem C_rot_false (v : List Bool) : C (false :: v) = 2 * C (rot (false :: v)) := by
  show C (false :: v) = 2 * C (v ++ [false])
  rw [C_snoc v false, C_cons false v]
  show 0 + 2 * C v = 2 * C v
  omega

/-- **Odd head: rotation is one step of `x ↦ (3x + 2^L − 3^a)/2`.**  Stated
without subtraction, so it holds for every word, positive gap or not. -/
theorem C_rot_true (v : List Bool) :
    2 * C (rot (true :: v)) + 3 ^ oddCount (true :: v)
      = 3 * C (true :: v) + 2 ^ (true :: v).length := by
  show 2 * C (v ++ [true]) + 3 ^ ((if true then 1 else 0) + oddCount v)
      = 3 * C (true :: v) + 2 ^ (v.length + 1)
  rw [C_snoc v true, C_cons true v]
  show 2 * (3 * C v + 2 ^ v.length) + 3 ^ (1 + oddCount v)
      = 3 * (3 ^ oddCount v + 2 * C v) + 2 ^ (v.length + 1)
  have h3 : (3:Nat) ^ (1 + oddCount v) = 3 * 3 ^ oddCount v := by
    rw [Nat.pow_add, Nat.pow_one]
  have h2 : (2:Nat) ^ (v.length + 1) = 2 * 2 ^ v.length := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h3, h2]
  omega

/-- The gap form of `C_rot_true`, available once the gap is positive. -/
theorem C_rot_true_gap {v : List Bool}
    (h : 3 ^ oddCount (true :: v) < 2 ^ (true :: v).length) :
    2 * C (rot (true :: v)) = 3 * C (true :: v) + gap (true :: v) := by
  have hk := C_rot_true v
  have hg : gap (true :: v) + 3 ^ oddCount (true :: v) = 2 ^ (true :: v).length := by
    show 2 ^ (true :: v).length - 3 ^ oddCount (true :: v)
        + 3 ^ oddCount (true :: v) = _
    omega
  omega

/-! ## 3. Cancelling `2` and `3` out of a common divisor -/

theorem dvd_three {k : Nat} (h : k ∣ 3) : k = 1 ∨ k = 3 := by
  obtain ⟨t, ht⟩ := h
  have hk : k ≤ 3 := Nat.le_of_dvd (by decide) ⟨t, ht⟩
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with h0 | h1 | h2 | h3
  · subst h0; omega
  · exact Or.inl h1
  · subst h2; omega
  · exact Or.inr h3

theorem gcd_three_eq_one {d : Nat} (h : ¬ (3 ∣ d)) : Nat.gcd 3 d = 1 := by
  rcases dvd_three (Nat.gcd_dvd_left 3 d) with h1 | h3
  · exact h1
  · exact absurd (h3 ▸ Nat.gcd_dvd_right 3 d) h

/-- A divisor prime to `3` absorbs a factor `3`. -/
theorem dvd_of_dvd_three_mul {d x : Nat} (h3 : ¬ (3 ∣ d)) (h : d ∣ 3 * x) : d ∣ x := by
  have h1 : d ∣ x * 3 := by rw [Nat.mul_comm]; exact h
  have h2 : d ∣ x * d := Nat.dvd_mul_left d x
  have hg := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left, gcd_three_eq_one h3, Nat.mul_one] at hg
  exact hg

/-- `2 ^ k` is never divisible by `3`. -/
theorem two_pow_mod_three (k : Nat) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    have hp : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rcases ih with h | h
    · right; rw [hp]; omega
    · left; rw [hp]; omega

theorem three_not_dvd_two_pow (L : Nat) : ¬ (3 ∣ 2 ^ L) := by
  intro h
  obtain ⟨k, hk⟩ := h
  rcases two_pow_mod_three L with h1 | h1 <;> omega

/-- `3` never divides a positive gap with at least one odd letter. -/
theorem three_not_dvd_gap {L a : Nat} (ha : 0 < a) (h : 3 ^ a < 2 ^ L) :
    ¬ (3 ∣ 2 ^ L - 3 ^ a) := by
  intro hdvd
  have h3a : (3:Nat) ∣ 3 ^ a := by
    obtain ⟨k, hk⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    exact ⟨3 ^ k, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
  have hsum : (2 ^ L - 3 ^ a) + 3 ^ a = 2 ^ L := by omega
  have h2 : (3:Nat) ∣ 2 ^ L := by
    obtain ⟨u, hu⟩ := hdvd
    obtain ⟨v, hv⟩ := h3a
    exact ⟨u + v, by rw [← hsum, hu, hv, Nat.mul_add]⟩
  exact three_not_dvd_two_pow L h2

/-! ## 4. `gcd(C, G)` is a rotation invariant -/

theorem two_pow_pos : ∀ t : Nat, 0 < 2 ^ t := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
    have : (2:Nat) ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    omega


/-- A positive gap of a nonempty word is odd. -/
theorem gap_odd {w : List Bool} (hlen : 0 < w.length)
    (h : 3 ^ oddCount w < 2 ^ w.length) : gap w % 2 = 1 := by
  have h3 : 3 ^ oddCount w % 2 = 1 := three_pow_odd _
  have h2 : (2:Nat) ^ w.length = 2 * 2 ^ (w.length - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, w.length = k + 1 := ⟨w.length - 1, by omega⟩
    rw [hk, Nat.pow_succ, Nat.mul_comm]
    have : k + 1 - 1 = k := by omega
    rw [this]
  show (2 ^ w.length - 3 ^ oddCount w) % 2 = 1
  omega

/-- **The rotation invariance of the gcd.**  Both letters are covered: the even
letter by cancelling `2`, the odd letter by cancelling `2` and then `3`. -/
theorem gcd_rot : ∀ {w : List Bool}, 3 ^ oddCount w < 2 ^ w.length →
    Nat.gcd (C (rot w)) (gap w) = Nat.gcd (C w) (gap w) := by
  intro w
  cases w with
  | nil => intro _; rfl
  | cons b v =>
    intro hpos
    have hlen : 0 < (b :: v).length := by simp
    have hodd : gap (b :: v) % 2 = 1 := gap_odd hlen hpos
    refine Nat.dvd_antisymm ?_ ?_
    · -- `gcd (C (rot w)) G  ∣  gcd (C w) G`
      have hA : Nat.gcd (C (rot (b :: v))) (gap (b :: v)) ∣ C (rot (b :: v)) :=
        Nat.gcd_dvd_left _ _
      have hG : Nat.gcd (C (rot (b :: v))) (gap (b :: v)) ∣ gap (b :: v) :=
        Nat.gcd_dvd_right _ _
      refine Nat.dvd_gcd ?_ hG
      cases b with
      | false =>
        rw [C_rot_false v]
        exact Nat.dvd_trans hA ⟨2, Nat.mul_comm _ _⟩
      | true =>
        have hlaw : 2 * C (rot (true :: v)) = 3 * C (true :: v) + gap (true :: v) :=
          C_rot_true_gap hpos
        have h2A : Nat.gcd (C (rot (true :: v))) (gap (true :: v))
            ∣ 3 * C (true :: v) + gap (true :: v) := by
          rw [← hlaw]
          exact Nat.dvd_trans hA ⟨2, Nat.mul_comm _ _⟩
        have h3B : Nat.gcd (C (rot (true :: v))) (gap (true :: v)) ∣ 3 * C (true :: v) := by
          have := dvd_sub_of_dvd h2A hG
          have heq : 3 * C (true :: v) + gap (true :: v) - gap (true :: v)
              = 3 * C (true :: v) := by omega
          rw [heq] at this
          exact this
        have hna : 0 < oddCount (true :: v) := by
          have e : oddCount (true :: v) = 1 + oddCount v := rfl
          omega
        have hn3 : ¬ (3 ∣ Nat.gcd (C (rot (true :: v))) (gap (true :: v))) := by
          intro hc
          exact three_not_dvd_gap hna hpos (Nat.dvd_trans hc hG)
        exact dvd_of_dvd_three_mul hn3 h3B
    · -- `gcd (C w) G  ∣  gcd (C (rot w)) G`
      have hB : Nat.gcd (C (b :: v)) (gap (b :: v)) ∣ C (b :: v) := Nat.gcd_dvd_left _ _
      have hG : Nat.gcd (C (b :: v)) (gap (b :: v)) ∣ gap (b :: v) := Nat.gcd_dvd_right _ _
      refine Nat.dvd_gcd ?_ hG
      have hoddg : Nat.gcd (C (b :: v)) (gap (b :: v)) % 2 = 1 :=
        odd_of_dvd_odd hodd hG
      cases b with
      | false =>
        refine odd_dvd_of_dvd_two_mul hoddg ?_
        rw [← C_rot_false v]
        exact hB
      | true =>
        refine odd_dvd_of_dvd_two_mul hoddg ?_
        rw [C_rot_true_gap hpos]
        exact Nat.dvd_add (Nat.dvd_trans hB ⟨3, Nat.mul_comm _ _⟩) hG

/-- The cycle condition is a property of the necklace, not of the word. -/
theorem gap_dvd_C_rot_iff {w : List Bool} (hpos : 3 ^ oddCount w < 2 ^ w.length) :
    gap w ∣ C (rot w) ↔ gap w ∣ C w := by
  constructor
  · intro h
    have h1 : gap w ∣ Nat.gcd (C (rot w)) (gap w) := Nat.dvd_gcd h (Nat.dvd_refl _)
    rw [gcd_rot hpos] at h1
    exact Nat.dvd_trans h1 (Nat.gcd_dvd_left _ _)
  · intro h
    have h1 : gap w ∣ Nat.gcd (C w) (gap w) := Nat.dvd_gcd h (Nat.dvd_refl _)
    rw [← gcd_rot hpos] at h1
    exact Nat.dvd_trans h1 (Nat.gcd_dvd_left _ _)

/-- `δ` is a rotation invariant. -/
theorem delta_rot {w : List Bool} (hpos : 3 ^ oddCount w < 2 ^ w.length) :
    delta (rot w) = delta w := by
  show gap (rot w) / Nat.gcd (C (rot w)) (gap (rot w)) = gap w / Nat.gcd (C w) (gap w)
  rw [gap_rot w, gcd_rot hpos]

/-! ## 5. Two classes closed -/

/-- A word with exactly one odd letter has a power of two for its accumulator. -/
theorem C_eq_two_pow_of_oddCount_one : ∀ {w : List Bool}, oddCount w = 1 →
    ∃ t : Nat, C w = 2 ^ t := by
  intro w
  induction w with
  | nil => intro h; exact absurd h (by decide)
  | cons b v ih =>
    intro h
    cases b with
    | true =>
      have hv : oddCount v = 0 := by
        have e : oddCount (true :: v) = 1 + oddCount v := rfl
        omega
      refine ⟨0, ?_⟩
      rw [C_cons true v, C_eq_zero_of_oddCount_zero hv, hv]
      rfl
    | false =>
      have hv : oddCount v = 1 := by
        have e : oddCount (false :: v) = 0 + oddCount v := rfl
        omega
      obtain ⟨t, ht⟩ := ih hv
      refine ⟨t + 1, ?_⟩
      rw [C_cons false v, ht]
      show 0 + 2 * 2 ^ t = 2 ^ (t + 1)
      rw [Nat.pow_succ]
      omega

/-- **One odd letter: never a cycle word.**  `C` is a power of two and the gap
is odd, so a gap above `1` cannot divide it. -/
theorem oddCount_one_no_cycle {w : List Bool} (h1 : oddCount w = 1)
    (hlen : 0 < w.length) (hpos : 3 ^ oddCount w < 2 ^ w.length)
    (hgt : 1 < gap w) : ¬ (gap w ∣ C w) := by
  intro hdvd
  obtain ⟨t, ht⟩ := C_eq_two_pow_of_oddCount_one h1
  rw [ht] at hdvd
  have := odd_dvd_two_pow (gap_odd hlen hpos) hdvd
  omega

/-- Pure arithmetic core of the two-odd-letter argument: `0 < C < 2 G` pins the
quotient at `1`. -/
theorem two_odd_arith {A B P m : Nat} (hA : 0 < A) (hA2 : A ≤ 2 * P)
    (hB : B ≤ 4 * P) (hP : 4 ≤ P) (hm : 3 * A + B = (8 * P - 9) * m) :
    3 * A + B = 8 * P - 9 := by
  have hmne : m ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hm
    omega
  have hmle : m ≤ 1 := by
    by_cases hm2 : 2 ≤ m
    · exfalso
      have h2 : (8 * P - 9) * 2 ≤ (8 * P - 9) * m := Nat.mul_le_mul_left _ hm2
      omega
    · omega
  have hm1 : m = 1 := by omega
  rw [hm1, Nat.mul_one] at hm
  exact hm

/-- An even accumulator cannot equal the odd gap. -/
theorem two_odd_parity {X Y P : Nat} (hP : 4 ≤ P) (h : 3 * (2 * X) + 2 * Y = 8 * P - 9) :
    False := by omega

/-- With `t₀ = 0` the equation forces `2 ^ t₁ = 8 P − 12 > 4 P`. -/
theorem two_odd_size {B P : Nat} (hP : 4 ≤ P) (hB : B ≤ 4 * P) (h : 3 * 1 + B = 8 * P - 9) :
    False := by omega

/-- **Two odd letters: never a cycle word, above `L = 4`.**  Stated in the
odd-step-time coordinates: `C = 3 · 2 ^ t₀ + 2 ^ t₁` and `G = 2 ^ L − 9`. -/
theorem two_odd_closed {L t0 t1 : Nat} (hL : 5 ≤ L) (h0 : t0 < t1) (h1 : t1 < L) :
    ¬ ((2 ^ L - 9) ∣ (3 * 2 ^ t0 + 2 ^ t1)) := by
  intro hdvd
  obtain ⟨k, hk⟩ : ∃ k, L = k + 3 := ⟨L - 3, by omega⟩
  subst hk
  have hk2 : 2 ≤ k := by omega
  have hP : (4:Nat) ≤ 2 ^ k := by
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    have h4' : (2:Nat) ^ 2 = 4 := by decide
    omega
  have e3 : (2:Nat) ^ (k + 3) = 8 * 2 ^ k := by
    rw [Nat.pow_add]
    have : (2:Nat) ^ 3 = 8 := by decide
    rw [this, Nat.mul_comm]
  have ht0 : (2:Nat) ^ t0 ≤ 2 * 2 ^ k := by
    have hle : (2:Nat) ^ t0 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpk : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have ht1 : (2:Nat) ^ t1 ≤ 4 * 2 ^ k := by
    have hle : (2:Nat) ^ t1 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpk : (2:Nat) ^ (k + 2) = 4 * 2 ^ k := by
      rw [Nat.pow_add]
      have h4' : (2:Nat) ^ 2 = 4 := by decide
      rw [h4', Nat.mul_comm]
    omega
  have hpos0 : 0 < (2:Nat) ^ t0 := two_pow_pos t0
  obtain ⟨m, hm⟩ := hdvd
  rw [e3] at hm
  have heq := two_odd_arith hpos0 ht0 ht1 hP hm
  -- `G` is odd, so `t₀ = 0`
  have ht0z : t0 = 0 := by
    by_cases hz : t0 = 0
    · exact hz
    · exfalso
      obtain ⟨u, hu⟩ : ∃ u, t0 = u + 1 := ⟨t0 - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, t1 = v + 1 := ⟨t1 - 1, by omega⟩
      have hA : (2:Nat) ^ t0 = 2 * 2 ^ u := by rw [hu, Nat.pow_succ, Nat.mul_comm]
      have hB : (2:Nat) ^ t1 = 2 * 2 ^ v := by rw [hv, Nat.pow_succ, Nat.mul_comm]
      rw [hA, hB] at heq
      exact two_odd_parity hP heq
  rw [ht0z] at heq
  have hone : (2:Nat) ^ 0 = 1 := rfl
  rw [hone] at heq
  exact two_odd_size hP ht1 heq

end GapRotation
end Collatz
