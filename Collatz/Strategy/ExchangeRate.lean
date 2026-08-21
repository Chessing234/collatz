import Collatz.Strategy.ThreeAdic

/-!
# The exchange-rate no-go: size plus valuations is not a rank either

`NoFiniteRanking.no_class_ranking` and `AnyModulusRanking.no_ranking_any_modulus`
kill every rank that factors through a **finite quotient**: the class of `−1`
returns to itself, higher up, at every modulus and every window length.  The
obvious next proposal escapes those results by not factoring through a quotient
at all — it combines a *size* term with the two *valuations* on which the
dynamics acts exactly:

`Φ(x) = α·log(x+1) + β·v₂(x+1) + γ·v₃(x+1)`.

This file shows that family fails too, for a reason visible in one line: an odd
step moves the triple `(log u, v₂(u), v₃(u))` by exactly `(log(3/2), −1, +1)`.
Size and the two valuations trade at a fixed rate, so the odd-step drift of `Φ`
is a *constant*, independent of `x`; the even steps, by contrast, move `v₂` and
`v₃` by unbounded amounts in both directions, which pins the sign of every
coefficient.  Three explicit witnesses are all it takes.

## What is formalised, and how it differs from the informal claim

The development has no reals, so the real-valued statement cannot be written
down verbatim.  Two substitutions are made, and both are recorded here rather
than smuggled in:

* **Integer coefficients.**  Each of `α, β, γ` is written as a difference of two
  naturals (`α = A₁ − A₂`, and so on) and the strict-decrease condition
  `Φ(T x) < Φ(x)` is cleared of subtraction into
  `Φ⁺(T x) + Φ⁻(x) < Φ⁺(x) + Φ⁻(T x)` (`Decreasing`).  This covers *every*
  integer sign pattern — hence, after clearing denominators, every rational one.
  Real coefficients with irrational ratios are **not** covered: that is the one
  genuine gap between the informal theorem and the formal one.
* **`log` becomes `⌊log₂⌋`.**  The size term is `A · lg (x+1)` for any `lg`
  meeting the specification `IsLog2` — `2 ^ lg n ≤ n < 2 ^ (lg n + 1)` — i.e.
  for any implementation of the integer binary logarithm.  This is a *different*
  family from the real one, not a weakening of it: at the witness
  `x = 2 ^ M − 2` the real `log₂` falls by almost exactly `1` while `⌊log₂⌋`
  does not move at all.  The underlying mechanism — a constant odd-step drift
  against unbounded even-step valuation jumps — is the same in both settings,
  but the theorem below is a theorem about the integer-logarithm family.

The valuations are likewise handled by specification rather than by definition:
`IsTwoVal f` says `2 ^ f n ∣ n` and `¬ 2 ^ (f n + 1) ∣ n`.  Nothing depends on
how `v₂` is computed, and no fuel recursion is needed anywhere.

## What comes out stronger than expected

The informal argument finishes by observing that `Φ(2 ^ N − 1) → −∞`, i.e. it
uses *boundedness below*.  That step turns out to be unnecessary.  Once the two
odd-step witnesses force `γ < β < 0`, the third witness — where `v₃(x+1)` is an
arbitrarily large `b` and `v₃(T x + 1)` is `0` — makes `Φ` **increase** by at
least `2b − |α|`, which is positive for large `b`.  So strict decrease alone is
already contradictory: `no_valuation_size_ranking` carries no boundedness
hypothesis, and it holds above every threshold `N`, so restricting the rank to
large `x` is no escape either.

## The three witnesses (every value checked numerically before formalising)

| witness | `x` | `(lg, v₂, v₃)(x+1)` | `(lg, v₂, v₃)(T x + 1)` | forces |
|---|---|---|---|---|
| even, `v₂` jump | `2 ^ (2m+1) − 2` | `(2m, 0, 0)` | `(2m, 2m, 0)` | `B₁ < B₂`, i.e. `β < 0` |
| odd, the exchange | `2 ^ (i+1) − 1` | `(i+1, i+1, 0)` | `(i+1, i, 1)` | `γ < β` |
| even, `v₃` collapse | `3 ^ (2c) − 1` | `(L, 0, 2c)` | `(L or L−1, 0, 0)` | `(C₂−C₁)·2c < A₁` |

The first two have `Δ⌊log₂⌋ = 0` exactly, so the size coefficient does not enter
them at all; the third has `Δ⌊log₂⌋ ∈ {−1, 0}`, so it enters only through the
bounded term `A₁`.  That is the whole proof.

## Reusable content

The odd-step exchange identities are proved standalone, being of independent
value: `twoVal_odd_step` (`v₂(u)` falls by exactly one) and `threeVal_odd_step`
(`v₃(u)` rises by exactly one), packaged as `odd_step_exchange`.  The
development already had these in divisibility form —
`OddRuns.oddRun_iff` and `ThreeAdic.three_pow_odd_step_iff`, the latter used
directly here — and what is new is the statement at the level of the valuations
themselves.  The even-step jumps are recorded as `twoVal_even_rise`,
`threeVal_even_rise` and `threeVal_even_fall`, each with an unbounded parameter;
together they say that the even steps supply and destroy valuation without
limit, which is precisely why no finite bookkeeping of `v₂` and `v₃` can work.
-/

namespace Collatz
namespace ExchangeRate

open Collatz Arith

/-! ## Specifications for the three ingredients

No valuation function is defined.  Every theorem quantifies over an arbitrary
function meeting the defining property, so the results apply to any
implementation and nothing depends on a recursion scheme. -/

/-- `f` computes the 2-adic valuation: `2 ^ f n` divides `n` and `2 ^ (f n + 1)`
does not. -/
def IsTwoVal (f : Nat → Nat) : Prop :=
  ∀ n : Nat, 0 < n → 2 ^ f n ∣ n ∧ ¬ (2 ^ (f n + 1) ∣ n)

/-- `f` computes the 3-adic valuation. -/
def IsThreeVal (f : Nat → Nat) : Prop :=
  ∀ n : Nat, 0 < n → 3 ^ f n ∣ n ∧ ¬ (3 ^ (f n + 1) ∣ n)

/-- `f` computes the integer binary logarithm `⌊log₂ n⌋`. -/
def IsLog2 (f : Nat → Nat) : Prop :=
  ∀ n : Nat, 0 < n → 2 ^ f n ≤ n ∧ n < 2 ^ (f n + 1)

/-! ## Elementary arithmetic -/

/-- Powers of two are strictly monotone, read backwards. -/
theorem lt_of_two_pow_lt {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · exact absurd h (Nat.not_lt.mpr (two_pow_le_two_pow h'))

/-- Cancellation on the right of a strict product inequality. -/
theorem lt_of_mul_lt_mul {a b c : Nat} (h : a * c < b * c) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul h' (Nat.le_refl c)))

/-- Powers of three form a divisibility chain. -/
theorem three_pow_dvd_three_pow {a b : Nat} (h : a ≤ b) : 3 ^ a ∣ 3 ^ b :=
  Nat.pow_dvd_pow 3 h

/-- The powers of two modulo three alternate `1, 2, 1, 2, …`. -/
theorem two_pow_mod_three : ∀ k : Nat, 2 ^ (2 * k) % 3 = 1 ∧ 2 ^ (2 * k + 1) % 3 = 2 := by
  intro k
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    have h1 : (2:Nat) ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
      have h : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h, two_pow_succ, two_pow_succ]
      omega
    have h2 : (2:Nat) ^ (2 * (k + 1) + 1) = 2 * 2 ^ (2 * (k + 1)) := two_pow_succ _
    omega

/-- Three never divides a power of two. -/
theorem two_pow_mod_three_ne_zero (k : Nat) : 2 ^ k % 3 ≠ 0 := by
  obtain ⟨m, hm⟩ : ∃ m : Nat, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
  have h := two_pow_mod_three m
  rcases hm with hm | hm <;> subst hm <;> omega

/-- The powers of three at even exponents are `1` modulo eight. -/
theorem three_pow_mod_eight : ∀ c : Nat, 3 ^ (2 * c) % 8 = 1 := by
  intro c
  induction c with
  | zero => decide
  | succ c ih =>
    have h1 : (3:Nat) ^ (2 * (c + 1)) = 9 * 3 ^ (2 * c) := by
      have h : 2 * (c + 1) = (2 * c + 1) + 1 := by omega
      rw [h, three_pow_succ, three_pow_succ]
      omega
    omega

/-! ## Uniqueness: the specifications pin the values -/

/-- The 2-adic valuation is determined by its defining pair of conditions. -/
theorem twoVal_eq {f : Nat → Nat} (hf : IsTwoVal f) {n k : Nat} (hn : 0 < n)
    (h1 : 2 ^ k ∣ n) (h2 : ¬ (2 ^ (k + 1) ∣ n)) : f n = k := by
  obtain ⟨g1, g2⟩ := hf n hn
  rcases Nat.lt_trichotomy (f n) k with h | h | h
  · exact absurd (Nat.dvd_trans (two_pow_dvd_two_pow (show f n + 1 ≤ k by omega)) h1) g2
  · exact h
  · exact absurd (Nat.dvd_trans (two_pow_dvd_two_pow (show k + 1 ≤ f n by omega)) g1) h2

/-- The 3-adic valuation is determined by its defining pair of conditions. -/
theorem threeVal_eq {f : Nat → Nat} (hf : IsThreeVal f) {n k : Nat} (hn : 0 < n)
    (h1 : 3 ^ k ∣ n) (h2 : ¬ (3 ^ (k + 1) ∣ n)) : f n = k := by
  obtain ⟨g1, g2⟩ := hf n hn
  rcases Nat.lt_trichotomy (f n) k with h | h | h
  · exact absurd (Nat.dvd_trans (three_pow_dvd_three_pow (show f n + 1 ≤ k by omega)) h1) g2
  · exact h
  · exact absurd (Nat.dvd_trans (three_pow_dvd_three_pow (show k + 1 ≤ f n by omega)) g1) h2

/-- The integer logarithm is determined by its defining pair of bounds. -/
theorem log2_eq {f : Nat → Nat} (hf : IsLog2 f) {n k : Nat}
    (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : f n = k := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (two_pow_pos k) h1
  obtain ⟨g1, g2⟩ := hf n hn
  have hle : f n < k + 1 := lt_of_two_pow_lt (Nat.lt_of_le_of_lt g1 h2)
  have hge : k < f n + 1 := lt_of_two_pow_lt (Nat.lt_of_le_of_lt h1 g2)
  omega

/-- A power of two has 2-adic valuation equal to its exponent. -/
theorem twoVal_two_pow {f : Nat → Nat} (hf : IsTwoVal f) (k : Nat) : f (2 ^ k) = k := by
  refine twoVal_eq hf (two_pow_pos k) (Nat.dvd_refl _) ?_
  intro h
  have h1 := le_of_dvd_pos (two_pow_pos k) h
  have h2 := two_pow_lt_two_pow (show k < k + 1 by omega)
  omega

/-- A power of two has vanishing 3-adic valuation. -/
theorem threeVal_two_pow {f : Nat → Nat} (hf : IsThreeVal f) (k : Nat) : f (2 ^ k) = 0 := by
  refine threeVal_eq hf (two_pow_pos k) (by simp) ?_
  intro h
  have h3 : (3:Nat) ^ (0 + 1) = 3 := by decide
  rw [h3] at h
  have := two_pow_mod_three_ne_zero k
  omega

/-- A number coprime to three has vanishing 3-adic valuation. -/
theorem threeVal_of_not_dvd {f : Nat → Nat} (hf : IsThreeVal f) {n : Nat} (hn : 0 < n)
    (h : ¬ (3 ∣ n)) : f n = 0 := by
  refine threeVal_eq hf hn (by simp) ?_
  intro hc
  have h3 : (3:Nat) ^ (0 + 1) = 3 := by decide
  rw [h3] at hc
  exact h hc

/-- An odd number has vanishing 2-adic valuation. -/
theorem twoVal_odd {f : Nat → Nat} (hf : IsTwoVal f) {n : Nat} (hn : 0 < n)
    (hodd : n % 2 = 1) : f n = 0 := by
  refine twoVal_eq hf hn (by simp) ?_
  intro h
  have h2 : (2:Nat) ^ (0 + 1) = 2 := by decide
  rw [h2] at h
  omega

/-! ## The odd-step exchange identities

These are the exact laws behind the no-go, stated on their own because they are
reusable: along an odd step the 2-adic valuation of `u = x + 1` pays exactly one
unit and the 3-adic valuation earns exactly one. -/

/-- **An odd step spends exactly one unit of `v₂(x+1)`.** -/
theorem twoVal_odd_step {f : Nat → Nat} (hf : IsTwoVal f) {x : Nat} (hx : x % 2 = 1) :
    f (acceleratedStep x + 1) + 1 = f (x + 1) := by
  have hid : 2 * (acceleratedStep x + 1) = 3 * (x + 1) := OddRuns.two_mul_succ_step hx
  obtain ⟨g1, g2⟩ := hf (x + 1) (by omega)
  -- the valuation is at least one, because `x + 1` is even
  have hk : 0 < f (x + 1) := by
    rcases Nat.eq_zero_or_pos (f (x + 1)) with h0 | h0
    · exfalso
      apply g2
      rw [h0]
      have h2 : (2:Nat) ^ (0 + 1) = 2 := by decide
      rw [h2]
      omega
    · exact h0
  obtain ⟨k, hkk⟩ : ∃ k : Nat, f (x + 1) = k + 1 := ⟨f (x + 1) - 1, by omega⟩
  rw [hkk] at g1 g2
  have hmain : f (acceleratedStep x + 1) = k := by
    refine twoVal_eq hf (by omega) ?_ ?_
    · -- `2 ^ k ∣ acceleratedStep x + 1`
      obtain ⟨c, hc⟩ := g1
      refine ⟨3 * c, ?_⟩
      have harith : 3 * (2 ^ (k + 1) * c) = 2 * (2 ^ k * (3 * c)) := by
        rw [two_pow_succ]
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have hdouble : 2 * (acceleratedStep x + 1) = 2 * (2 ^ k * (3 * c)) := by
        rw [hid, hc, harith]
      omega
    · -- `¬ 2 ^ (k+1) ∣ acceleratedStep x + 1`
      intro h
      apply g2
      refine OddRuns.dvd_of_three_mul (k + 1 + 1) (x + 1) ?_
      rw [← hid]
      obtain ⟨c, hc⟩ := h
      refine ⟨c, ?_⟩
      rw [hc, two_pow_succ (k + 1)]
      simp [Nat.mul_assoc]
  omega

/-- **An odd step earns exactly one unit of `v₃(x+1)`.**  A restatement of
`ThreeAdic.three_pow_odd_step_iff` at the level of the valuation. -/
theorem threeVal_odd_step {f : Nat → Nat} (hf : IsThreeVal f) {x : Nat} (hx : x % 2 = 1) :
    f (acceleratedStep x + 1) = f (x + 1) + 1 := by
  obtain ⟨g1, g2⟩ := hf (x + 1) (by omega)
  refine threeVal_eq hf (by omega) ?_ ?_
  · exact (ThreeAdic.three_pow_odd_step_iff hx (f (x + 1))).mp g1
  · intro h
    exact g2 ((ThreeAdic.three_pow_odd_step_iff hx (f (x + 1) + 1)).mpr h)

/-- **The exchange, in one statement.**  Along an odd step the two valuations of
`u = x + 1` move by exactly `−1` and `+1`.  Their sum is therefore invariant, and
no combination of them alone can measure progress across odd steps. -/
theorem odd_step_exchange {f g : Nat → Nat} (hf : IsTwoVal f) (hg : IsThreeVal g)
    {x : Nat} (hx : x % 2 = 1) :
    f (acceleratedStep x + 1) + 1 = f (x + 1) ∧
    g (acceleratedStep x + 1) = g (x + 1) + 1 :=
  ⟨twoVal_odd_step hf hx, threeVal_odd_step hg hx⟩

/-! ## The even steps move both valuations by unbounded amounts

The odd step is rigid; the even step is not.  Each of the three families below
carries an unbounded parameter, and together they pin the sign of every
coefficient in the proposed rank. -/

/-- **`v₂` rises without bound at an even step.**  At `x = 2 ^ (K+1) − 2` the
shift `x + 1` is odd, and a single halving turns it into `2 ^ K`. -/
theorem twoVal_even_rise {f : Nat → Nat} (hf : IsTwoVal f) (K : Nat) :
    f ((2 ^ (K + 1) - 2) + 1) = 0 ∧
      f (acceleratedStep (2 ^ (K + 1) - 2) + 1) = K := by
  have hK : (0:Nat) < 2 ^ K := two_pow_pos K
  have hsucc : (2:Nat) ^ (K + 1) = 2 * 2 ^ K := two_pow_succ K
  have hstep : acceleratedStep (2 ^ (K + 1) - 2) = 2 ^ K - 1 := by
    rw [acceleratedStep, if_pos (show (2 ^ (K + 1) - 2) % 2 = 0 by omega)]
    omega
  refine ⟨twoVal_odd hf (by omega) (by omega), ?_⟩
  rw [hstep, show (2:Nat) ^ K - 1 + 1 = 2 ^ K by omega]
  exact twoVal_two_pow hf K

/-- **`v₃` rises without bound at an even step.**  At `x = 2 · 3 ^ b − 2` the
shift is `2 · 3 ^ b − 1`, coprime to three, and a single halving turns it into
`3 ^ b`.  An even step can inject an arbitrary amount of 3-divisibility. -/
theorem threeVal_even_rise {f : Nat → Nat} (hf : IsThreeVal f) {b : Nat} (hb : 0 < b) :
    f ((2 * 3 ^ b - 2) + 1) = 0 ∧
      f (acceleratedStep (2 * 3 ^ b - 2) + 1) = b := by
  have hb3 : (0:Nat) < 3 ^ b := three_pow_pos b
  have hodd : (3:Nat) ^ b % 2 = 1 := three_pow_odd b
  have hsplit : (3:Nat) ^ b = 3 * 3 ^ (b - 1) := by
    have hb1 : b = (b - 1) + 1 := by omega
    rw [show (3:Nat) ^ b = 3 ^ ((b - 1) + 1) by rw [← hb1], three_pow_succ]
  have hstep : acceleratedStep (2 * 3 ^ b - 2) = 3 ^ b - 1 := by
    rw [acceleratedStep, if_pos (show (2 * 3 ^ b - 2) % 2 = 0 by omega)]
    omega
  constructor
  · refine threeVal_of_not_dvd hf (by omega) ?_
    intro h
    obtain ⟨c, hc⟩ := h
    omega
  · rw [hstep, show (3:Nat) ^ b - 1 + 1 = 3 ^ b by omega]
    refine threeVal_eq hf hb3 (Nat.dvd_refl _) ?_
    intro h
    have h1 := le_of_dvd_pos hb3 h
    have h2 := three_pow_lt_three_pow (show b < b + 1 by omega)
    omega

/-- **`v₃` falls without bound at an even step.**  At `x = 3 ^ b − 1` the shift is
`3 ^ b` itself, and a single halving destroys all of it: `(3 ^ b + 1)/2` is
coprime to three.  This is the witness that forbids a negative `γ`. -/
theorem threeVal_even_fall {f : Nat → Nat} (hf : IsThreeVal f) {b : Nat} (hb : 0 < b) :
    f ((3 ^ b - 1) + 1) = b ∧ f (acceleratedStep (3 ^ b - 1) + 1) = 0 := by
  have hb3 : (0:Nat) < 3 ^ b := three_pow_pos b
  have hodd : (3:Nat) ^ b % 2 = 1 := three_pow_odd b
  have hsplit : (3:Nat) ^ b = 3 * 3 ^ (b - 1) := by
    have hb1 : b = (b - 1) + 1 := by omega
    rw [show (3:Nat) ^ b = 3 ^ ((b - 1) + 1) by rw [← hb1], three_pow_succ]
  have hstep : acceleratedStep (3 ^ b - 1) = (3 ^ b - 1) / 2 := by
    rw [acceleratedStep, if_pos (show (3 ^ b - 1) % 2 = 0 by omega)]
  have hval : 2 * (acceleratedStep (3 ^ b - 1) + 1) = 3 ^ b + 1 := by
    rw [hstep]; omega
  constructor
  · rw [show (3:Nat) ^ b - 1 + 1 = 3 ^ b by omega]
    refine threeVal_eq hf hb3 (Nat.dvd_refl _) ?_
    intro h
    have h1 := le_of_dvd_pos hb3 h
    have h2 := three_pow_lt_three_pow (show b < b + 1 by omega)
    omega
  · refine threeVal_of_not_dvd hf (by omega) ?_
    intro h
    obtain ⟨c, hc⟩ := h
    omega

/-! ## The proposed rank, with signed coefficients

`Rank lg tv th A B C x = A · lg(x+1) + B · v₂(x+1) + C · v₃(x+1)`.  A rank with
integer coefficients `(α, β, γ) = (A₁ − A₂, B₁ − B₂, C₁ − C₂)` strictly decreases
at `x` exactly when `Decreasing` holds — the subtraction-free form of
`Φ(T x) < Φ(x)`. -/

/-- One half of a proposed rank. -/
def Rank (lg tv th : Nat → Nat) (A B C x : Nat) : Nat :=
  A * lg (x + 1) + B * tv (x + 1) + C * th (x + 1)

/-- Strict decrease of the signed rank `Φ = Rank(A₁,B₁,C₁) − Rank(A₂,B₂,C₂)`
across one accelerated step, written without subtraction. -/
def Decreasing (lg tv th : Nat → Nat) (A₁ B₁ C₁ A₂ B₂ C₂ x : Nat) : Prop :=
  Rank lg tv th A₁ B₁ C₁ (acceleratedStep x) + Rank lg tv th A₂ B₂ C₂ x <
    Rank lg tv th A₁ B₁ C₁ x + Rank lg tv th A₂ B₂ C₂ (acceleratedStep x)

/-! ## Witness one: the even `v₂` jump forces `β < 0` -/

/-- **The `v₂`-jump witness.**  At `x = 2 ^ (2m+1) − 2` the integer logarithm does
not move, `v₃` vanishes at both ends, and `v₂` jumps from `0` to `2m`.  The only
surviving term is `β · 2m`, so strict decrease forces `β < 0`. -/
theorem coeff_two_neg {lg tv th : Nat → Nat} (hlg : IsLog2 lg) (htv : IsTwoVal tv)
    (hth : IsThreeVal th) {A₁ B₁ C₁ A₂ B₂ C₂ m : Nat} (_hm : 0 < m)
    (hdec : Decreasing lg tv th A₁ B₁ C₁ A₂ B₂ C₂ (2 ^ (2 * m + 1) - 2)) : B₁ < B₂ := by
  have hK : (0:Nat) < 2 ^ (2 * m) := two_pow_pos (2 * m)
  have hsucc : (2:Nat) ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := two_pow_succ (2 * m)
  have hmod := two_pow_mod_three m
  have hstep : acceleratedStep (2 ^ (2 * m + 1) - 2) = 2 ^ (2 * m) - 1 := by
    rw [acceleratedStep, if_pos (show (2 ^ (2 * m + 1) - 2) % 2 = 0 by omega)]
    omega
  have hshift : (2:Nat) ^ (2 * m) - 1 + 1 = 2 ^ (2 * m) := by omega
  -- the six readings
  have hlg1 : lg (2 ^ (2 * m + 1) - 2 + 1) = 2 * m :=
    log2_eq hlg (by omega) (by omega)
  have hlg2 : lg (acceleratedStep (2 ^ (2 * m + 1) - 2) + 1) = 2 * m := by
    rw [hstep, hshift]
    exact log2_eq hlg (Nat.le_refl _) (two_pow_lt_two_pow (by omega))
  obtain ⟨htv1, htv2⟩ := twoVal_even_rise htv (2 * m)
  rw [show 2 * m + 1 = 2 * m + 1 from rfl] at htv1 htv2
  have hth1 : th (2 ^ (2 * m + 1) - 2 + 1) = 0 := by
    refine threeVal_of_not_dvd hth (by omega) ?_
    intro h
    obtain ⟨c, hc⟩ := h
    omega
  have hth2 : th (acceleratedStep (2 ^ (2 * m + 1) - 2) + 1) = 0 := by
    rw [hstep, hshift]
    exact threeVal_two_pow hth (2 * m)
  simp only [Decreasing, Rank, hlg1, hlg2, htv1, htv2, hth1, hth2] at hdec
  exact lt_of_mul_lt_mul (show B₁ * (2 * m) < B₂ * (2 * m) by omega)

/-! ## Witness two: the odd exchange forces `γ < β` -/

/-- **The exchange witness.**  At `x = 2 ^ (i+1) − 1` the step is odd and lands on
`3 · 2 ^ i`, so the integer logarithm again does not move while `v₂` falls by one
and `v₃` rises by one.  The drift is the constant `γ − β`, and strict decrease
forces `γ < β`. -/
theorem coeff_three_lt_two {lg tv th : Nat → Nat} (hlg : IsLog2 lg) (htv : IsTwoVal tv)
    (hth : IsThreeVal th) {A₁ B₁ C₁ A₂ B₂ C₂ i : Nat}
    (hdec : Decreasing lg tv th A₁ B₁ C₁ A₂ B₂ C₂ (2 ^ (i + 1) - 1)) :
    C₁ + B₂ < B₁ + C₂ := by
  have hi : (0:Nat) < 2 ^ i := two_pow_pos i
  have hsucc : (2:Nat) ^ (i + 1) = 2 * 2 ^ i := two_pow_succ i
  have hsucc2 : (2:Nat) ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := two_pow_succ (i + 1)
  have hodd : (2 ^ (i + 1) - 1) % 2 = 1 := by omega
  have hu : (2:Nat) ^ (i + 1) - 1 + 1 = 2 ^ (i + 1) := by omega
  -- the successor after the odd step is exactly `3 · 2 ^ i`
  have hid : 2 * (acceleratedStep (2 ^ (i + 1) - 1) + 1) = 3 * (2 ^ (i + 1) - 1 + 1) :=
    OddRuns.two_mul_succ_step hodd
  rw [hu] at hid
  have hnext : acceleratedStep (2 ^ (i + 1) - 1) + 1 = 3 * 2 ^ i := by omega
  -- readings at `x`
  have hlg1 : lg (2 ^ (i + 1) - 1 + 1) = i + 1 := by
    rw [hu]
    exact log2_eq hlg (Nat.le_refl _) (two_pow_lt_two_pow (by omega))
  have htv1 : tv (2 ^ (i + 1) - 1 + 1) = i + 1 := by
    rw [hu]; exact twoVal_two_pow htv (i + 1)
  have hth1 : th (2 ^ (i + 1) - 1 + 1) = 0 := by
    rw [hu]; exact threeVal_two_pow hth (i + 1)
  -- readings at `T x`, via the exchange identities
  have htv2 : tv (acceleratedStep (2 ^ (i + 1) - 1) + 1) = i := by
    have h := twoVal_odd_step htv hodd
    rw [htv1] at h
    omega
  have hth2 : th (acceleratedStep (2 ^ (i + 1) - 1) + 1) = 1 := by
    have h := threeVal_odd_step hth hodd
    rw [hth1] at h
    omega
  have hlg2 : lg (acceleratedStep (2 ^ (i + 1) - 1) + 1) = i + 1 := by
    rw [hnext]
    exact log2_eq hlg (by omega) (by omega)
  simp only [Decreasing, Rank, hlg1, hlg2, htv1, htv2, hth1, hth2] at hdec
  have hb1 : B₁ * (i + 1) = B₁ * i + B₁ := by rw [Nat.mul_add, Nat.mul_one]
  have hb2 : B₂ * (i + 1) = B₂ * i + B₂ := by rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## Witness three: the `v₃` collapse contradicts a negative `γ` -/

/-- **The collapse witness.**  At `x = 3 ^ (2c) − 1` the valuation `v₃(x+1) = 2c`
is destroyed by a single even step, while the integer logarithm moves by at most
one and `v₂` stays at zero throughout.  Strict decrease therefore bounds
`(C₂ − C₁) · 2c` by the single constant `A₁`. -/
theorem coeff_size_bound {lg tv th : Nat → Nat} (hlg : IsLog2 lg) (htv : IsTwoVal tv)
    (hth : IsThreeVal th) {A₁ B₁ C₁ A₂ B₂ C₂ c : Nat} (hc : 0 < c)
    (hdec : Decreasing lg tv th A₁ B₁ C₁ A₂ B₂ C₂ (3 ^ (2 * c) - 1)) :
    C₂ * (2 * c) < C₁ * (2 * c) + A₁ := by
  have hb3 : (0:Nat) < 3 ^ (2 * c) := three_pow_pos (2 * c)
  have hodd : (3:Nat) ^ (2 * c) % 2 = 1 := three_pow_odd (2 * c)
  have h8 : (3:Nat) ^ (2 * c) % 8 = 1 := three_pow_mod_eight c
  have hstep : acceleratedStep (3 ^ (2 * c) - 1) = (3 ^ (2 * c) - 1) / 2 := by
    rw [acceleratedStep, if_pos (show (3 ^ (2 * c) - 1) % 2 = 0 by omega)]
  have hval : 2 * (acceleratedStep (3 ^ (2 * c) - 1) + 1) = 3 ^ (2 * c) + 1 := by
    rw [hstep]; omega
  -- valuations at both ends
  obtain ⟨hth1, hth2⟩ := threeVal_even_fall hth (show 0 < 2 * c by omega)
  have htv1 : tv (3 ^ (2 * c) - 1 + 1) = 0 := twoVal_odd htv (by omega) (by omega)
  have htv2 : tv (acceleratedStep (3 ^ (2 * c) - 1) + 1) = 0 :=
    twoVal_odd htv (by omega) (by omega)
  -- name the two logarithms and bound their difference
  obtain ⟨L, hLdef⟩ : ∃ L : Nat, lg (3 ^ (2 * c) - 1 + 1) = L := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Nat, lg (acceleratedStep (3 ^ (2 * c) - 1) + 1) = D := ⟨_, rfl⟩
  obtain ⟨hL1, hL2⟩ := hlg (3 ^ (2 * c) - 1 + 1) (by omega)
  obtain ⟨hD1, hD2⟩ := hlg (acceleratedStep (3 ^ (2 * c) - 1) + 1) (by omega)
  rw [hLdef] at hL1 hL2
  rw [hDdef] at hD1 hD2
  rw [show (3:Nat) ^ (2 * c) - 1 + 1 = 3 ^ (2 * c) by omega] at hL1 hL2
  have hsuccD : (2:Nat) ^ (D + 1 + 1) = 2 * 2 ^ (D + 1) := two_pow_succ (D + 1)
  have hDL : D ≤ L := by
    have h : (2:Nat) ^ D < 2 ^ (L + 1) := by omega
    have := lt_of_two_pow_lt h
    omega
  have hLD : L ≤ D + 1 := by
    have h : (2:Nat) ^ L < 2 ^ (D + 1 + 1) := by omega
    have := lt_of_two_pow_lt h
    omega
  -- the size terms are pinned to within the constant `A₁`
  have hA1 : A₁ * L ≤ A₁ * D + A₁ := by
    have h : A₁ * L ≤ A₁ * (D + 1) := Nat.mul_le_mul (Nat.le_refl A₁) hLD
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hA2 : A₂ * D ≤ A₂ * L := Nat.mul_le_mul (Nat.le_refl A₂) hDL
  simp only [Decreasing, Rank, hLdef, hDdef, htv1, htv2, hth1, hth2] at hdec
  omega

/-! ## The no-go -/

/-- **The explicit failing witness.**  For every integer choice of the three
coefficients — written as differences `A₁ − A₂`, `B₁ − B₂`, `C₁ − C₂` of
naturals, so that all sign patterns are covered — and every threshold `N`, an
explicit `x > N` is produced at which the rank
`Φ(x) = α·⌊log₂(x+1)⌋ + β·v₂(x+1) + γ·v₃(x+1)` fails to decrease.

Which of the three families supplies the witness is decided by the coefficients
themselves, and the case analysis is over decidable comparisons of naturals, so
nothing classical is used. -/
theorem exists_failing_witness {lg tv th : Nat → Nat}
    (hlg : IsLog2 lg) (htv : IsTwoVal tv) (hth : IsThreeVal th)
    (A₁ B₁ C₁ A₂ B₂ C₂ N : Nat) :
    ∃ x : Nat, N < x ∧ ¬ Decreasing lg tv th A₁ B₁ C₁ A₂ B₂ C₂ x := by
  have hw1 : N < 2 ^ (2 * (N + 1) + 1) - 2 := by
    have h1 : N + 2 < 2 ^ (N + 2) := lt_two_pow_self (N + 2)
    have h2 : (2:Nat) ^ (N + 2) ≤ 2 ^ (2 * (N + 1) + 1) := two_pow_le_two_pow (by omega)
    omega
  have hw2 : N < 2 ^ (N + 1) - 1 := by
    have h1 : N + 1 < 2 ^ (N + 1) := lt_two_pow_self (N + 1)
    omega
  rcases Nat.lt_or_ge B₁ B₂ with hB | hB
  · rcases Nat.lt_or_ge (C₁ + B₂) (B₁ + C₂) with hC | hC
    · -- both odd-step constraints hold, so `γ ≤ −2`; the collapse witness fails
      have hgap : C₁ + 2 ≤ C₂ := by omega
      have hcpos : 0 < A₁ + N + 1 := by omega
      have hw3 : N < 3 ^ (2 * (A₁ + N + 1)) - 1 := by
        have h1 : (2:Nat) ^ (2 * (A₁ + N + 1)) ≤ 3 ^ (2 * (A₁ + N + 1)) :=
          two_pow_le_three_pow (2 * (A₁ + N + 1))
        have h2 : 2 * (A₁ + N + 1) < 2 ^ (2 * (A₁ + N + 1)) :=
          lt_two_pow_self (2 * (A₁ + N + 1))
        omega
      refine ⟨3 ^ (2 * (A₁ + N + 1)) - 1, hw3, ?_⟩
      intro hd
      have hfinal := coeff_size_bound hlg htv hth hcpos hd
      have hmono : (C₁ + 2) * (2 * (A₁ + N + 1)) ≤ C₂ * (2 * (A₁ + N + 1)) :=
        Nat.mul_le_mul hgap (Nat.le_refl _)
      have hexp : (C₁ + 2) * (2 * (A₁ + N + 1))
          = C₁ * (2 * (A₁ + N + 1)) + 2 * (2 * (A₁ + N + 1)) :=
        Nat.add_mul C₁ 2 (2 * (A₁ + N + 1))
      omega
    · exact ⟨2 ^ (N + 1) - 1, hw2, fun hd =>
        absurd (coeff_three_lt_two hlg htv hth hd) (Nat.not_lt.mpr hC)⟩
  · exact ⟨2 ^ (2 * (N + 1) + 1) - 2, hw1, fun hd =>
      absurd (coeff_two_neg hlg htv hth (by omega) hd) (Nat.not_lt.mpr hB)⟩

/-- **No size-plus-valuations rank decreases.**  For every integer choice of the
coefficients and every threshold `N`, the rank
`Φ(x) = α·⌊log₂(x+1)⌋ + β·v₂(x+1) + γ·v₃(x+1)` fails to decrease strictly
somewhere above `N`.

The three witnesses run in sequence: `2 ^ (2N+3) − 2` forces `β < 0`,
`2 ^ (N+1) − 1` forces `γ < β` — hence `γ ≤ β − 1 ≤ −2` — and then
`3 ^ (2c) − 1` with `c` large forces `2 · 2c ≤ (−γ)·2c < α⁺`, which fails.

No boundedness hypothesis is used: strict decrease above any threshold is by
itself contradictory. -/
theorem no_valuation_size_ranking {lg tv th : Nat → Nat}
    (hlg : IsLog2 lg) (htv : IsTwoVal tv) (hth : IsThreeVal th)
    (A₁ B₁ C₁ A₂ B₂ C₂ N : Nat) :
    ¬ (∀ x : Nat, N < x → Decreasing lg tv th A₁ B₁ C₁ A₂ B₂ C₂ x) := by
  intro hdec
  obtain ⟨x, hx, hfail⟩ := exists_failing_witness hlg htv hth A₁ B₁ C₁ A₂ B₂ C₂ N
  exact hfail (hdec x hx)

/-- **The purely non-negative family, restated.**  With `α, β, γ ≥ 0` — the shape
an unsigned search would propose — the failure is immediate and needs only the
first witness: at `x = 2 ^ (2m+1) − 2` the rank does not move at all when `β = 0`
and rises when `β > 0`. -/
theorem no_nonneg_ranking {lg tv th : Nat → Nat}
    (hlg : IsLog2 lg) (htv : IsTwoVal tv) (hth : IsThreeVal th) (A B C N : Nat) :
    ¬ (∀ x : Nat, N < x →
        Rank lg tv th A B C (acceleratedStep x) < Rank lg tv th A B C x) := by
  intro hdec
  have hpos : N < 2 ^ (2 * (N + 1) + 1) - 2 := by
    have h1 : N + 2 < 2 ^ (N + 2) := lt_two_pow_self (N + 2)
    have h2 : (2:Nat) ^ (N + 2) ≤ 2 ^ (2 * (N + 1) + 1) := two_pow_le_two_pow (by omega)
    omega
  have hd : Decreasing lg tv th A B C 0 0 0 (2 ^ (2 * (N + 1) + 1) - 2) := by
    simp only [Decreasing, Rank, Nat.zero_mul, Nat.add_zero]
    exact hdec _ hpos
  have := coeff_two_neg hlg htv hth (show 0 < N + 1 by omega) hd
  omega

end ExchangeRate
end Collatz
