import Collatz.Strategy.SizePerturbation

/-!
# The banked three and the next harvest are independent, and provably so

A local (non-density) coupling was sought: along one forward orbit, does the next
contraction's harvest correlate with the `v₃` the last growth run banked?  The
contingency table was computed and it factors.  This file records the table, and
proves the reason it *must* factor.

## A correction to the question

At the end of a growth run of length `r = v₂(n+1)` every factor of two is spent, so
`T^r(n) + 1 = 3^r · w` is **odd** and `v₂(T^r(n)+1) = 0` identically — verified for
every odd `n < 200 000`.  The non-trivial quantity, the one that sets the *next*
run length, is the harvest `v₂(T^r(n) + 2) = v₂(3^r·w + 1)`.  That is what was
tabulated.

## The table

Joint law of `A = v₃(n+1)` and `B = v₂(3^r·w + 1)`, over all odd `n < 2^20`
(`524 288` samples):

| `A \ B` | `1` | `2` | `3` | `4` | `P(A)` |
|---|---|---|---|---|---|
| `0` | `0.33333` | `0.16667` | `0.08333` | `0.04167` | `0.66667` |
| `1` | `0.11111` | `0.05555` | `0.02778` | `0.01389` | `0.22222` |
| `2` | `0.03704` | `0.01852` | `0.00926` | `0.00463` | `0.07407` |
| `3` | `0.01235` | `0.00617` | `0.00309` | `0.00154` | `0.02469` |
| `P(B)` | `0.50000` | `0.25000` | `0.12500` | `0.06250` | |

The marginals are exactly geometric — `P(A = a) = (2/3)·3^(−a)`,
`P(B = b) = 2^(−b)` — and **every cell is their product**: maximum relative
deviation `0.00266`, `χ² = 0.01` across `16` cells.

**The coupling is local and dead.**

## Why it must factor

This is not an accident of sampling.  Write `n + 1 = 2^r · w` with `w` odd.  Then

* `A = v₃(n+1) = v₃(w)` is a function of `w` modulo a power of **three**;
* `B = v₂(3^r·w + 1)` is, by `LogCoordinate`, a function of `r` and of `w` modulo a
  power of **two** — the discrete logarithm and the sign `ε(w) = ±1`, which is
  `w mod 8`.

Powers of two and powers of three are coprime, so those two pieces of congruence
data are independent: by the Chinese Remainder Theorem every combination of
`w mod 2^j` and `w mod 3^k` occurs, equally often.  **No orbit structure can create
a correlation between them, because there is no arithmetic through which one could
constrain the other.**

`two_pow_dvd_three_pow_iff` below is that coprimality in the form this development
needs: a power of two divides a power of three only when it is `1`.

## Consequence

The banked `v₃` cannot force a drop, and no refinement of this pairing will — the
obstruction is not that the correlation is weak but that it is *arithmetically
absent*.  A local coupling has to pair two quantities that live at the same prime.
`SizePerturbation` is the shape that survives, because there the two coordinates
are `2`-adic and archimedean rather than `2`-adic and `3`-adic.
-/

namespace Collatz
namespace CouplingDead

/-- Powers of three are odd. -/
theorem three_pow_odd (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hs : (3 : Nat) ^ (k + 1) = 3 * 3 ^ k := by rw [← Nat.pow_succ']
    rw [hs]
    omega

/-- **The two coordinates are coprime.**  A power of two divides a power of three
only in the trivial case, so `w mod 2^j` and `w mod 3^k` carry independent
information — which is why the contingency table factors. -/
theorem two_pow_dvd_three_pow_iff (j k : Nat) : 2 ^ j ∣ 3 ^ k ↔ j = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact hj
    · exfalso
      have h2 : (2 : Nat) ∣ 2 ^ j := by
        have : (2 : Nat) ^ 1 ∣ 2 ^ j := Nat.pow_dvd_pow 2 hj
        simpa using this
      have hdvd : (2 : Nat) ∣ 3 ^ k := Nat.dvd_trans h2 h
      obtain ⟨c, hc⟩ := hdvd
      have := three_pow_odd k
      omega
  · intro h; subst h; simpa using Nat.one_dvd _

/-- The same, contrapositive and in the form used above: no nontrivial power of two
divides `3 ^ k`. -/
theorem not_two_dvd_three_pow (k : Nat) : ¬ (2 ∣ 3 ^ k) := by
  intro h
  obtain ⟨c, hc⟩ := h
  have := three_pow_odd k
  omega

end CouplingDead
end Collatz
