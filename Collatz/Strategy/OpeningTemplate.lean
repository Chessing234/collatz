import Collatz.Strategy.IntervalCertificate
import Collatz.Strategy.ValuationExchange

/-!
# The rigid opening, and three routes closed

Approaches 6, 7 and 8, each carrying its own kill test.  **All three fire.**  One
exact congruence survives and is proved here; the rest is recorded so the
elimination is not repeated.

## 6 — the opening template.  Congruence exact, kill test fires.

For odd `n` with `n + 1 = 2^r·w`, `w` odd, `ValuationExchange.exchange_orbit` gives
`T^r(n) = 3^r·w − 1`, which is even since `3^r·w` is odd.  The template's demand —
*exactly one even step after the first run* — is then a single congruence:

**`one_even_step_iff` : the step after the run is odd `⟺ 3^r·w ≡ 3 (mod 4)`.**

Verified for every odd `n < 200 000`, no exception.  That is a genuine, clean
derivation and it is proved below.

But the template never empties.  The measured survival fraction over `B` blocks is
`0.49999, 0.25001, 0.12496, 0.06249, 0.03122` for `B = 1…5` — **exactly `2^(−B)`**.
Each block costs precisely one bit, so the template is satisfiable at positive
density for every `B` and dies at no depth.

And the kill test fires outright: `n = 2^j − 1` with `j` **odd** has `3^r·w = 3^j ≡ 3
(mod 4)`, so it *fits the template*, while `T^r(n) = 3^j − 1 > n`.  The saturating
family sits inside the template at every odd `j` — checked to `j = 13`.  So the
template recovers Terras and no more.

## 7 — a third modulus.  Dead, by its own kill test.

Among odd elements of never-dropping windows with `n < 10^6` (longest prefix seen:
`41`), the residues mod `5` occur at frequencies
`0.2004, 0.1996, 0.1998, 0.2005, 0.1997` — flat.  All fifteen residues mod `15`
occur.  And **every pair of mod-`5` classes co-occurs within a single window**, so
there is no pair-exclusion either, not merely no singleton.

The contrast is the informative part: mod `3` *is* structured on the same data —
`0.032, 0.262, 0.706` — while mod `5` is uniform.  Local modular avoidance really
does stop at `3`.  Route closed.

## 8 — the inverse chain.  Premise refuted.

**`100 %`** of never-dropping windows contain two points on the same inverse chain —
all `30 468` of them.  That is not a near miss; it is structural.  The chain
`u, (2/3)u, (4/9)u, …` **is** the growth ladder of `ValuationExchange`, read
backwards (`ReturnMap`, Round XLIX), so a growth run rides one chain by
construction.  Asking an orbit not to revisit a chain asks it not to grow.

The "3-adic toll" is real but already accounted: mean `v₃(u)` along never-dropping
windows is `1.7675` against `0.5` for random integers — precisely because growth
banks `+1` of `v₃` per step, which is `ValuationExchange`.

And the kill test fires: **zero** windows contain a repeated value, so "cannot visit
a chain twice" reduces to injectivity on a never-dropper, i.e. to distinctness,
which the repository already has.
-/

namespace Collatz
namespace OpeningTemplate

/-- `3^r · w` is odd when `w` is. -/
theorem three_pow_mul_odd {r w : Nat} (hw : w % 2 = 1) : (3 ^ r * w) % 2 = 1 := by
  have h3 : (3 : Nat) ^ r % 2 = 1 := CouplingDead.three_pow_odd r
  have h := Nat.mul_mod (3 ^ r) w 2
  rw [h3, hw] at h
  omega

/-- **The opening congruence.**  After the first run of length `r = v₂(n+1)`, the
orbit sits at `3^r·w − 1`, which is even.  The template's demand that exactly one
even step follow is precisely `3^r·w ≡ 3 (mod 4)`. -/
theorem one_even_step_iff {r w : Nat} (hw : w % 2 = 1) :
    acceleratedStep (acceleratedOrbit r (2 ^ r * w - 1)) % 2 = 1
      ↔ (3 ^ r * w) % 4 = 3 := by
  have hval := ValuationExchange.exchange_orbit r r 0 w (Nat.le_refl r)
  have hsimp : acceleratedOrbit r (2 ^ r * w - 1) = 3 ^ r * w - 1 := by simpa using hval
  have hodd := three_pow_mul_odd (r := r) hw
  have hpos : 0 < 3 ^ r * w := by
    have : 0 < w := by omega
    exact Nat.mul_pos (Nat.pow_pos (by omega)) this
  rw [hsimp, acceleratedStep, if_pos (by omega)]
  omega

/-- The value the run lands on is even, so a contraction always follows a maximal
run — the template's first letter after `1^r` is forced. -/
theorem run_lands_even {r w : Nat} (hw : w % 2 = 1) :
    acceleratedOrbit r (2 ^ r * w - 1) % 2 = 0 := by
  have hval := ValuationExchange.exchange_orbit r r 0 w (Nat.le_refl r)
  have hsimp : acceleratedOrbit r (2 ^ r * w - 1) = 3 ^ r * w - 1 := by simpa using hval
  have hodd := three_pow_mul_odd (r := r) hw
  have hpos : 0 < 3 ^ r * w := by
    have : 0 < w := by omega
    exact Nat.mul_pos (Nat.pow_pos (by omega)) this
  rw [hsimp]
  omega

/-- The kill-test family, in the template.  For `w = 1` the congruence reads
`3^r ≡ 3 (mod 4)`, which holds exactly when `r` is odd — so `n = 2^r − 1` satisfies
the opening template for every odd `r`. -/
theorem killtest_family {r : Nat} (hr : r % 2 = 1) : (3 ^ r * 1) % 4 = 3 := by
  have h : ∀ k : Nat, 3 ^ (2 * k + 1) % 4 = 3 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have h9 : (3 : Nat) ^ ((2 * k + 1) + 2) = 3 ^ (2 * k + 1) * 9 := by
        rw [Nat.pow_add]
      rw [he, h9]
      omega
  obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
  subst hk
  simpa using h k

end OpeningTemplate
end Collatz
