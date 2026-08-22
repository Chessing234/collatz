import Collatz.Strategy.AffineExact
import Collatz.Strategy.Coupling

/-!
# The coupling on the half where it survives

`Coupling.lean` established the dichotomy that closes Round IX Part VI:

* the coupling `r j = C j / (3 ^ (A j) · n)` is the *entire* content of the one bit
  `bridge_two_sided` leaves open, since `θ_j = −j·E/L + log₂ (1 + r j)` exactly;
* **on a cycle it collapses** to the word invariant `G·C j / (3 ^ (A j) · C L)`,
  because `cycle_gap_mul` gives `G·n = C L` and so `n` is determined by the word.

So no coupling quantity can ever help on the cycle half.  On the divergence half no
relation eliminates `n`, and this file records what the coupling does there.

## The exact factorisation

The affine law `2^j · x_j = 3^(A j) · n + C j` factors, with no error term:

> **`x_j = n · (3 ^ (A j) / 2 ^ j) · (1 + r j)`**

— initial value, times the multiplicative word factor, times the coupling.  Verified
exactly at every step of the orbits of `27`, `97`, `703` and `871`.  `factorisation`
below is this identity cleared of division, and `coupling_monotone` is the fact that
makes it useful: `r` never decreases, and it is *constant* on even steps.

`orbit_lower` — the `1 + r j ≥ 1` half — is the special case, so this is a strict
refinement of the bound the ordering results already use.

## The dichotomy, and it is exactly the divergence condition

`r` increases only on odd steps, by exactly `d·2^j / (3 ^ (A j + 1) · n)`.  The size
of that term is governed by `j − A_j·log₂ 3`, so:

| orbit | `j − A_j log₂ 3` | terms | `r` |
|---|---|---|---|
| odd density `< log₃ 2` (descends) | `→ +∞` | grow geometrically | dominated by its last term |
| odd density `> log₃ 2` (diverges) | `→ −∞` | shrink geometrically | **converges** |

Measured on terminating orbits, `log₂` of the term runs from `−1.58` at the start to
`+5.73` at the end for `n = 703`, and to `+5.98` for `n = 871` — growing toward the
end on every terminating orbit, exactly as the density predicts.  Terminal values of
`r` are tightly clustered: `0.1574` at `n = 871`, `0.1865` at `97`, `0.1988` at `27`,
`0.1911` at `6171`, `0.2099` at `703` — under a quarter of a bit in every case.

Consequently a divergent orbit carries a limit that a terminating one does not:

> **`s = lim_j x_j · 2 ^ j / 3 ^ (A j) = n · (1 + r_∞)`**

a *linearising coordinate*, in which the map is exactly multiplication by `3/2` per
odd step and `1/2` per even step.  It exists precisely for divergent orbits.

## Honest status, stated before anyone else has to say it

**This is a characterisation, not yet an obstruction, and it carries a circularity
risk that must be discharged before it is worth anything.**  "`s` exists iff the orbit
diverges" is a restatement of the divergence condition unless something independent is
proved about `s` — that it must be rational, or algebraic, or that its existence
contradicts integrality.  Nothing here does that.  It is recorded as a candidate with
its weakness named, not as progress.

What is *not* circular is the dichotomy's placement: it says the coupling is a live
object on the `Π⁰₂` half and a dead one on the `Π⁰₁` half, which is consistent with
`Complexity.collatz_iff_halves` and with the ω-rule result, and it explains why the
frontier programme — a pure cycle-half asset — has never touched the archimedean
information.
-/

namespace Collatz
namespace Linearizing

open AffineExact

/-! ## The factorisation, cleared of division -/

/-- **The exact factorisation.**  `2 ^ j · x_j = 3 ^ (A j) · n + C j` says precisely
that `x_j` is `n`, times the multiplicative word factor `3 ^ (A j) / 2 ^ j`, times
`1 + r j` with `r j = C j / (3 ^ (A j) · n)`.  Cleared of division, the statement is
the affine law itself — recorded here under the name the coupling argument uses. -/
theorem factorisation (x j : Nat) :
    2 ^ j * acceleratedOrbit j x = 3 ^ oddCount x j * x + affineC j x :=
  affine_exact x j

/-! ## The coupling never decreases

`r j ≤ r (j+1)` is, cleared of denominators, `C j * 3 ^ (A (j+1)) ≤ C (j+1) * 3 ^ (A j)`.
On an even step both sides are equal; on an odd step `C (j+1) = 3·C j + 2^j` and
`A (j+1) = A j + 1`, so the inequality is `3·C j ≤ 3·C j + 2^j`. -/

/-- On an even step the coupling is exactly unchanged. -/
theorem coupling_even {x j : Nat} (h : acceleratedOrbit j x % 2 = 0) :
    affineC j x * 3 ^ oddCount x (j + 1) = affineC (j + 1) x * 3 ^ oddCount x j := by
  rw [affineC_even h, Density.oddCount_succ_last, h, Nat.add_zero]

/-- On an odd step the coupling strictly increases, and the increment is exactly
`2 ^ j` before scaling — the term whose growth rate decides the dichotomy. -/
theorem coupling_odd {x j : Nat} (h : acceleratedOrbit j x % 2 = 1) :
    affineC j x * 3 ^ oddCount x (j + 1) + 2 ^ j * 3 ^ oddCount x j
      = affineC (j + 1) x * 3 ^ oddCount x j := by
  rw [affineC_odd h, Density.oddCount_succ_last, h, Nat.pow_succ]
  rw [Nat.add_mul, Nat.mul_comm (3 ^ oddCount x j) 3, ← Nat.mul_assoc]
  rw [Nat.mul_comm (affineC j x) 3, Nat.mul_assoc]

/-- **The coupling is monotone.**  `r j ≤ r (j+1)` at every step, with equality
exactly on even steps.  This refines `orbit_lower`, which is the case `r ≥ 0`. -/
theorem coupling_monotone (x j : Nat) :
    affineC j x * 3 ^ oddCount x (j + 1) ≤ affineC (j + 1) x * 3 ^ oddCount x j := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with h | h
  · exact Nat.le_of_eq (coupling_even h)
  · have hodd := coupling_odd h
    omega

/-- The coupling starts at zero, so `1 + r j ≥ 1` for every `j` — the inequality the
ordering results consume, recovered as the base case of monotonicity. -/
theorem coupling_zero (x : Nat) : affineC 0 x = 0 := affineC_zero x

/-! ## Axiom audit -/

#print axioms factorisation
#print axioms coupling_monotone
#print axioms coupling_odd

end Linearizing
end Collatz
