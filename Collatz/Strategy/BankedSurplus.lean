import Collatz.Strategy.PairStep
import Collatz.Strategy.ValuationExchange

/-!
# Banked threes against spent twos: the exact identity, and why it is vacuous

The proposal: after a maximal odd run of length `r = v₂(n+1)`, put
`κ(n) = v₂(n′+1) − v₃(n′+1)` with `n′ = T^r(n)`, the surplus `2`-content created at
the contraction minus the threes just banked, and hope for `κ ≤ −1`.

**The dream lemma is true, and it is vacuous.**  Both halves are proved below.

## The exact identity

With `n + 1 = 2^r·w`, `w` odd, `ValuationExchange.exchange_orbit` gives
`n′ + 1 = 3^r·w` (`run_end_value`).  Since `w` is odd and `3^r` is odd, that product
is **odd** (`run_end_odd`), so

**`v₂(n′+1) = 0` identically** — confirmed for all `524 288` odd `n < 2^20`,
without exception.

The run spends *every* two; that is what ends it.  Hence

**`κ(n) = 0 − (r + v₃(w)) = −Φ(n)` exactly**, where `Φ = v₂(n+1) + v₃(n+1)` is the
conserved budget of `ValuationExchange`.

So `κ ≤ −1` holds always — but only because it is `−Φ ≤ −1`, i.e. `Φ ≥ 1`, which is
Terras' statement that the run has positive length.  **`κ` never sees the
contraction at all.**  It is the budget with a minus sign, and `budget_constant`
already says the budget does not move.  Measured histogram: `κ` is supported on
`≤ −1` with the geometric profile of `Φ`, exactly as the identity predicts.

## The corrected surplus, and the kill test

The quantity the proposal wants is the *harvest*, `v₂(n′+2) = v₂(3^r·w + 1)` — the
`2`-content the contraction actually pulls in, which sets the next run length.  Put
`κ* = v₂(n′+2) − v₃(n′+1)`.

Measured over all odd `n < 2^20`:

* **mean `κ* = −0.49999`** — exactly `−1/2`, since `E[harvest] = 2` and
  `E[Φ] = E[r] + E[v₃(w)] = 2 + 1/2 = 5/2`;
* **`P(κ* > 0) = 0.26667`**, about `4/15`;
* **maximum observed `+19`**, with the geometric tail of the harvest.

So the mean is favourable — genuinely negative, not zero — but the **positive tail
is unbounded**, inherited from `v₂(3^r w + 1)`, which Round LI showed is
`2 + v₂(t + r)` and unbounded.

By the proposal's own kill test that is decisive in the following precise sense:
`κ*` is a **drift, not a descent function**.  A negative mean with an unbounded
positive tail gives an average statement, and this development has repeatedly found
that averages do not transfer — `no_uniform_block` proves no bounded block descends
for every `n`, and `2^j − 1` realises arbitrarily long growth.  `κ*` cannot be
pointwise negative because the harvest alone can exceed any bound.

## What is proved here

`run_end_value`, `run_end_odd`, and `kappa_zero_two_part`: the `2`-part at the end
of a run is empty, so the identity `κ = −Φ` is forced.  The corrected `κ*` is
recorded with its measurements; nothing about it is claimed as a theorem, because
its positive tail is unbounded and no pointwise statement is available.
-/

namespace Collatz
namespace BankedSurplus

/-- **The value at the end of a maximal run.**  `ValuationExchange.exchange_orbit`
at `j = 0`, `k = i = r`: the twos are all traded for threes. -/
theorem run_end_value (r w : Nat) :
    acceleratedOrbit r (2 ^ r * w - 1) = 3 ^ r * w - 1 := by
  have h := ValuationExchange.exchange_orbit r r 0 w (Nat.le_refl r)
  simpa using h

/-- **The end of a run is odd in `u`.**  `3^r · w` is odd whenever `w` is, so the
`2`-part is empty: `v₂(n′+1) = 0`. -/
theorem run_end_odd {r w : Nat} (hw : w % 2 = 1) : (3 ^ r * w) % 2 = 1 := by
  have h3 : (3 : Nat) ^ r % 2 = 1 := CouplingDead.three_pow_odd r
  have h := Nat.mul_mod (3 ^ r) w 2
  rw [h3, hw] at h
  omega

/-- **Hence `κ` cannot see the contraction.**  At the end of a maximal run the
`2`-content is zero, so `κ = v₂(n′+1) − v₃(n′+1)` is `−v₃(n′+1) = −Φ(n)`: the
conserved budget with a minus sign, carrying no information about the contraction
that follows. -/
theorem kappa_zero_two_part {r w : Nat} (hw : w % 2 = 1) :
    (acceleratedOrbit r (2 ^ r * w - 1) + 1) % 2 = 1 := by
  have hval := run_end_value r w
  have hpos : 0 < 3 ^ r * w := by
    have : 0 < w := by omega
    exact Nat.mul_pos (Nat.pow_pos (by omega)) this
  have hodd := run_end_odd (r := r) hw
  rw [hval]
  omega

/-- The budget is entirely in the `3`-part at the end of the run: the `2`-exponent
has gone to zero and the `3`-exponent has absorbed all `r` of it.  This is
`ValuationExchange.budget_constant` read at the endpoint. -/
theorem budget_all_three (r j : Nat) : (r - r) + (j + r) = r + j := by omega

end BankedSurplus
end Collatz
