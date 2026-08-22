import Collatz.Strategy.ExchangeRate

/-!
# Canonical heights: which postulate Collatz violates

In arithmetic dynamics one attaches to a morphism `f : P¹ → P¹` of degree
`d ≥ 2` the **canonical height**

    ĥ_f(x) = lim_n h(f^n x) / d^n,

which satisfies the functional equation `ĥ_f(f x) = d · ĥ_f(x)` *exactly*, agrees
with the naive Weil height up to `O(1)`, and vanishes precisely on the
preperiodic points.  Northcott then makes `ĥ_f⁻¹([0, B])` finite, and the whole
theory of preperiodic points follows.

This file settles whether any of that transfers to the accelerated map
`T(x) = x/2` (even), `(3x+1)/2` (odd).  It does not, and the failure is not a
technicality: it can be localised to a single postulate.

## The two postulates

* **(FE)** the functional equation `ĥ(f x) = d · ĥ(x)` with `d ≥ 2`;
* **(WC)** the Weil comparison `ĥ = h + O(1)`, which is what makes `ĥ` a height
  at all (finite fibres below a bound — Northcott).

For a genuine degree-`d` morphism the two are compatible because the naive
height *contracts* along backward orbits: every `y ∈ f⁻¹(x)` has
`h(y) ≈ h(x)/d`.  Collatz has the opposite behaviour.  The even branch gives
`T(2x) = x`, so `2x` is always a preimage of `x`, and the backward chain

    x, 2x, 4x, 8x, …

has naive height *growing* by `log 2` at each step while (FE) forces `ĥ` to
*shrink* by the factor `d` at each step.  The two postulates are therefore
contradictory, and this is exactly the postulate that fails:

> **preimages have height `h/d`.**  Collatz's even branch doubles the naive
> height of a preimage instead of dividing it.

`canonical_height_vanishes` proves the sharpest integral form: the *only*
`H : Nat → Nat` satisfying (FE) with any integer degree `k ≥ 2` is `H ≡ 0`.  No
appeal to (WC) is needed for that; `no_height_comparison` then records the clash
with (WC) itself.  So the classical construction does not merely fail to
converge here — its output is forced to be the zero function, and the Northcott
characterisation "`ĥ = 0` iff preperiodic" degenerates to a tautology.

## Why the limit itself is the discrepancy

Taking `d = 1` — the honest degree of a piecewise affine map — the Tate limit
`lim (log T^n x − n·E)` is, by the exact affine identity
`2 ^ L · T^L x = 3 ^ a · x + C` (`AffineExact.affine_exact`), equal to
`log x + log 3 · (a − L/2)` up to a bounded error: the fluctuation of the
candidate canonical height *is* the discrepancy path `D(j) = A(j) − (a/L)·j`,
already governed by `Discrepancy.bridge_two_sided`.  The limit therefore fails
to exist for the same reason the discrepancy fails to converge, and the object
is admissible-rule-dead: it is a function of `D`.

## Degree one leaves only a first integral

With `d = 1` the functional equation reads `H(T x) = H(x)`: a conserved
quantity.  `invariant_of_reaches_one` and `second_orbit_of_nonconstant` show
that such an `H` is constant exactly when every orbit reaches `1`, so producing
a non-trivial degree-one canonical height is not a route to the conjecture — it
is *equivalent* to it.

## No local decomposition escapes

A classical height decomposes as `h = Σ_v λ_v`.  The Collatz analogue
`α·log₂ x + β·v₂ + γ·v₃` is precisely the family killed by
`ExchangeRate.no_valuation_size_ranking`, which forbids strict *decrease* above
any threshold; `no_valuation_size_increasing` below records that the same
theorem forbids strict *increase*, by swapping the two coefficient triples.
Since a non-vanishing height obeying (FE) with `k ≥ 2` increases strictly at
every step, a local-height decomposition in those three places is an instance of
that no-go, not an escape from it.
-/

namespace Collatz
namespace Height

/-! ## The backward doubling chain -/

/-- The even branch: `2x` is always a `T`-preimage of `x`.  This is the whole
obstruction in one line — a backward step *raises* the naive height. -/
theorem step_two_mul (x : Nat) : acceleratedStep (2 * x) = x := by
  have h : (2 * x) % 2 = 0 := by omega
  simp only [acceleratedStep, if_pos h]
  omega

/-- Iterating the backward doubling chain: `2 ^ m · x` returns to `x` after `m`
accelerated steps. -/
theorem orbit_two_pow_mul : ∀ (m x : Nat), acceleratedOrbit m (2 ^ m * x) = x := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have hpow : (2:Nat) ^ (m + 1) * x = 2 * (2 ^ m * x) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    rw [acceleratedOrbit_succ, hpow, step_two_mul, ih]

/-! ## (FE) alone forces the zero function -/

/-- One backward step of the functional equation: `H(x) = k · H(2x)`. -/
theorem fun_eq_double {H : Nat → Nat} {k : Nat}
    (hfun : ∀ x, H (acceleratedStep x) = k * H x) (x : Nat) :
    H x = k * H (2 * x) := by
  have h := hfun (2 * x)
  rwa [step_two_mul] at h

/-- The chain form: `H(x) = k ^ m · H(2 ^ m · x)` for every `m`. -/
theorem fun_eq_chain {H : Nat → Nat} {k : Nat}
    (hfun : ∀ x, H (acceleratedStep x) = k * H x) :
    ∀ (m x : Nat), H x = k ^ m * H (2 ^ m * x) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have hpow : (2:Nat) * (2 ^ m * x) = 2 ^ (m + 1) * x := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    have hstep : H (2 ^ m * x) = k * H (2 ^ (m + 1) * x) := by
      have h := fun_eq_double hfun (2 ^ m * x)
      rw [hpow] at h
      exact h
    have hassoc : ∀ y : Nat, k ^ m * (k * y) = k ^ (m + 1) * y := by
      intro y
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [ih x, hstep]
    exact hassoc _

/-- **The canonical-height no-go.**  For every integer degree `k ≥ 2`, the only
`H : Nat → Nat` satisfying the exact functional equation
`H (T x) = k · H x` is the zero function.

The proof is the backward doubling chain: `H x = k ^ m · H (2 ^ m · x)`, so a
single nonzero value of `H` would make `H x` divisible by — hence at least —
`k ^ m ≥ 2 ^ m` for every `m`.

This is the precise sense in which no canonical height exists for `T`.  It is
unconditional, uses no property of the odd branch at all, and is therefore
insensitive to every asset of the soundness filter: it holds verbatim for
`(3x+d)/2` for every `d`. -/
theorem canonical_height_vanishes {H : Nat → Nat} {k : Nat} (hk : 2 ≤ k)
    (hfun : ∀ x, H (acceleratedStep x) = k * H x) : ∀ x, H x = 0 := by
  intro x
  rcases Nat.eq_zero_or_pos (H x) with hzero | hpos
  · exact hzero
  · exfalso
    have hchain := fun_eq_chain hfun (H x) x
    rcases Nat.eq_zero_or_pos (H (2 ^ H x * x)) with h0 | htail
    · rw [h0, Nat.mul_zero] at hchain
      omega
    · have hge : k ^ H x ≤ k ^ H x * H (2 ^ H x * x) :=
        Nat.le_mul_of_pos_right _ htail
      have hk2 : (2:Nat) ^ H x ≤ k ^ H x := Nat.pow_le_pow_left hk (H x)
      have hlt : H x < 2 ^ H x := Arith.lt_two_pow_self (H x)
      omega

/-- **(FE) and (WC) are contradictory.**  There is no `H` satisfying the
functional equation for a degree `k ≥ 2` together with the Weil comparison in
its weakest useful form — that `H x` is at least the bit length of `x`, which is
exactly what makes `H` a height with finite fibres.

This is the failure named in the header: `canonical_height_vanishes` kills
`H`, and a height that vanishes cannot dominate the naive height. -/
theorem no_height_comparison {H : Nat → Nat} {k : Nat} (hk : 2 ≤ k)
    (hfun : ∀ x, H (acceleratedStep x) = k * H x)
    (hcmp : ∀ m x : Nat, 2 ^ m ≤ x → m ≤ H x) : False := by
  have hzero := canonical_height_vanishes hk hfun 2
  have h1 : 1 ≤ H 2 := hcmp 1 2 (by decide)
  omega

/-! ## The archimedean degree is not an integer, from either side -/

/-- **`T` is not expanding.**  No integer factor `k ≥ 1` bounds `T` from below
above any threshold: the even branch halves.  A degree-`d` morphism expands the
archimedean absolute value by `d`; `T` does not expand by anything. -/
theorem no_expansion_factor {k c : Nat} (h : ∀ x, c < x → k * x ≤ acceleratedStep x) :
    k = 0 := by
  have hx : c < 2 * c + 2 := by omega
  have hstep : acceleratedStep (2 * c + 2) = c + 1 := by
    have h2 : (2 * c + 2) % 2 = 0 := by omega
    simp only [acceleratedStep, if_pos h2]
    omega
  have hle := h (2 * c + 2) hx
  rw [hstep] at hle
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · exact hk0
  · exfalso
    have : 2 * c + 2 ≤ k * (2 * c + 2) := Nat.le_mul_of_pos_left _ hk1
    omega

/-- **`T` is not contracting either.**  Any integer factor bounding `T` from
above must be at least `1`: the odd branch multiplies by `3/2`.  Together with
`no_expansion_factor` this is the straddle — the two branches have archimedean
multipliers on opposite sides of `1`, so no power of `|·|` is a cocycle for any
degree, which is the structural reason the Tate limit has nothing to converge
to. -/
theorem contraction_factor_pos {k c : Nat} (h : ∀ x, c < x → acceleratedStep x ≤ k * x) :
    1 ≤ k := by
  have hx : c < 2 * c + 3 := by omega
  have hstep : acceleratedStep (2 * c + 3) = 3 * c + 5 := by
    have h2 : ¬ (2 * c + 3) % 2 = 0 := by omega
    simp only [acceleratedStep, if_neg h2]
    omega
  have hle := h (2 * c + 3) hx
  rw [hstep] at hle
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · exfalso
    rw [hk0, Nat.zero_mul] at hle
    omega
  · exact hk1

/-! ## Degree one: a canonical height is a first integral -/

/-- An invariant `H` is constant along orbits. -/
theorem invariant_orbit {H : Nat → Nat} (hinv : ∀ x, H (acceleratedStep x) = H x) :
    ∀ (n x : Nat), H (acceleratedOrbit n x) = H x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [acceleratedOrbit_succ, ih (acceleratedStep x), hinv x]

/-- **Degree one gives a tautology.**  If every orbit reaches `1` then every
`T`-invariant `H` is constant.  So the degree-one canonical height carries no
information *given* the conjecture. -/
theorem invariant_of_reaches_one {H : Nat → Nat}
    (hinv : ∀ x, H (acceleratedStep x) = H x)
    (hreach : ∀ x : Nat, 1 ≤ x → ∃ n : Nat, acceleratedOrbit n x = 1) :
    ∀ x : Nat, 1 ≤ x → H x = H 1 := by
  intro x hx
  obtain ⟨n, hn⟩ := hreach x hx
  have := invariant_orbit hinv n x
  rw [hn] at this
  exact this.symm

/-- …and conversely, a non-constant invariant *is* a counterexample: the
conjecture and the non-existence of a degree-one canonical height are the same
statement.  Building one is therefore not a strategy. -/
theorem second_orbit_of_nonconstant {H : Nat → Nat}
    (hinv : ∀ x, H (acceleratedStep x) = H x) {x : Nat} (hx : H x ≠ H 1) :
    ∀ n : Nat, acceleratedOrbit n x ≠ 1 := by
  intro n hn
  apply hx
  have := invariant_orbit hinv n x
  rw [hn] at this
  exact this.symm

/-! ## Local heights are the killed family, restated for increase -/

/-- **`ExchangeRate.no_valuation_size_ranking`, in the increasing direction.**
Swapping the two coefficient triples turns strict decrease of
`Φ = Rank(A₁,B₁,C₁) − Rank(A₂,B₂,C₂)` into strict increase, so the same no-go
forbids both.

This is what closes the "local height" proposal.  A height decomposing over the
places `∞, 2, 3` as `α·⌊log₂ x⌋ + β·v₂ + γ·v₃` and obeying the functional
equation with degree `k ≥ 2` would satisfy `Φ(T x) ≥ 2·Φ(x) > Φ(x)` wherever
`Φ > 0` — a strict increase above a threshold, which this theorem forbids for
every integer choice of `α, β, γ`.  The local-height candidate is an instance of
the exchange-rate no-go, not an escape from it. -/
theorem no_valuation_size_increasing {lg tv th : Nat → Nat}
    (hlg : ExchangeRate.IsLog2 lg) (htv : ExchangeRate.IsTwoVal tv)
    (hth : ExchangeRate.IsThreeVal th) (A₁ B₁ C₁ A₂ B₂ C₂ N : Nat) :
    ¬ (∀ x : Nat, N < x →
        ExchangeRate.Rank lg tv th A₁ B₁ C₁ x
            + ExchangeRate.Rank lg tv th A₂ B₂ C₂ (acceleratedStep x) <
          ExchangeRate.Rank lg tv th A₁ B₁ C₁ (acceleratedStep x)
            + ExchangeRate.Rank lg tv th A₂ B₂ C₂ x) := by
  intro hinc
  refine ExchangeRate.no_valuation_size_ranking hlg htv hth A₂ B₂ C₂ A₁ B₁ C₁ N ?_
  intro x hx
  have h := hinc x hx
  simp only [ExchangeRate.Decreasing]
  omega

end Height
end Collatz
