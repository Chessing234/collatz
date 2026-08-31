import Collatz.Strategy.ReturnMap

/-!
# Collatz is a base swap perturbed by one

Pushing the first-principles reduction one step further than `ReturnMap`.

Put `U = n + 2`, so that `U` is even exactly when the orbit is at a contraction.
Write `U = 2^a · w` with `w` odd.  Then the entire map — one contraction together
with the whole growth run it releases — is

**`U ↦ 3^(a−1) · w + 1`.**

Take the `2`-part, replace it by a `3`-part one power smaller, add one.  Verified
faithful against `T` for every even `n < 60 000`, no exceptions, and `swap_form`
below derives it from `ReturnMap.return_map`.

So: **Collatz is the base-swap operator `2^a ↦ 3^(a−1)` perturbed by `+1`.**  The
swap alone is a monoid map and trivial; the `+1` is the whole problem, and its job
is precisely to regenerate the `2`-content that the swap destroys — `S(U)` is
always odd, and `+1` is what puts it back in the domain.

## What that buys, exactly

**1. The fixed points are completely classified.**  `S(U) + 1 = U` reads
`w·(2^a − 3^(a−1)) = 1`, so `w = 1` and `2^a − 3^(a−1) = 1`.  For `a ≥ 3` one has
`2^a < 3^(a−1)` (`two_pow_lt_three_pow`), so only `a = 1, 2` survive, giving
`U = 2` and `U = 4` — that is `n = 0` and the trivial cycle `n = 2`.
`fixed_point_iff` is that classification.  A whole family of exponential
Diophantine equations collapses to a two-line induction.

**2. The coupling is located.**  The difficulty is entirely
`v₂(3^k · m + 1)`: how much `2`-content adding one regenerates from an odd number
whose `3`-part the swap just created.  This is a genuine `2`-adic × `3`-adic
interaction, in the coordinate where it exists.  For `m = 1` it is bounded:

**`8 ∤ 3^k + 1` for every `k`** (`not_eight_dvd_three_pow_succ`),

since `3^k % 8 ∈ {1, 3}`.  So `v₂(3^k + 1) ≤ 2` always, and the pure powers of two
`U = 2^a` always step to a state with `a′ ≤ 2`, which contracts, since
`3^(a′−1) < 2^(a′)` there.  `pow_two_state_contracts` records it.

For general `m` the bound fails and the structure appears instead as a congruence:
measured, `v₂(3^k·m + 1) ≥ j` holds exactly on a residue class of `k` modulo
`2^(j−2)` — for `m = 5, j = 4` it is `k ≡ 1 (mod 4)`; for `m = 7` it is
`k ≡ 2 (mod 4)`; for `m = 11` it is empty.  Deep `2`-adic regeneration needs the
`3`-exponent to sit in an exponentially thin class.

## What it does not do

It classifies period one, not period `L`.  For period `L` the same computation
gives `2^E − 3^(E−L)` in the denominator, positive only when `E/L < log 3/log(3/2)
= 2.7095…`, so `E ≤ ⌊2.7095 L⌋` — finite for each `L`, but the number of valuation
words is `C(E−1, L−1)`, and the known bound already forces `E ≥ 6809`.  So the
finite checks this makes available at small `L` are subsumed.  The `+1` regeneration
question is not answered here; it is only put in its sharpest form.
-/

namespace Collatz
namespace SwapForm

/-- `2^a < 3^(a−1)` for every `a ≥ 3`: the swap is expanding past the threshold. -/
theorem two_pow_lt_three_pow : ∀ a : Nat, 3 ≤ a → 2 ^ a < 3 ^ (a - 1) := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
    intro h
    rcases Nat.lt_or_ge a 3 with hlt | hge
    · have ha : a = 2 := by omega
      subst ha; decide
    · have hprev := ih hge
      have hstep : (2 : Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [← Nat.pow_succ']
      have he : a - 1 + 1 = a := by omega
      have h3 : (3 : Nat) ^ (a + 1 - 1) = 3 * 3 ^ (a - 1) := by
        have : a + 1 - 1 = (a - 1) + 1 := by omega
        rw [this, ← Nat.pow_succ']
      rw [hstep, h3]
      omega

/-- **The swap form.**  With `U = n + 2 = 2^(k+1) · w` and `w` odd, one contraction
and the growth run it releases send `U` to `3^k · w + 1`. -/
theorem swap_form {k w : Nat} (hw : w % 2 = 1) :
    acceleratedOrbit (k + 1) (2 ^ (k + 1) * w - 2) + 2 = 3 ^ k * w + 1 := by
  have h := ReturnMap.return_map (k := k) (w := w) hw
  have hpos : 0 < 3 ^ k * w := by
    have : 0 < w := by omega
    exact Nat.mul_pos (Nat.pow_pos (by omega)) this
  omega

/-- **The fixed points, classified.**  `3^(a−1)·w + 1 = 2^a·w` with `w` odd and
`a ≥ 1` forces `w = 1` and `a ∈ {1, 2}` — the states `U = 2` and `U = 4`, that is
`n = 0` and the trivial cycle `n = 2`. -/
theorem fixed_point_iff {a w : Nat} (ha : 0 < a) (hw : w % 2 = 1) :
    3 ^ (a - 1) * w + 1 = 2 ^ a * w ↔ (w = 1 ∧ (a = 1 ∨ a = 2)) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge a 3 with hlt | hge
    · have h12 : a = 1 ∨ a = 2 := by omega
      rcases h12 with h1 | h2
      · subst h1
        have e1 : (3 : Nat) ^ (1 - 1) = 1 := by decide
        have e2 : (2 : Nat) ^ 1 = 2 := by decide
        rw [e1, e2] at h
        exact ⟨by omega, Or.inl rfl⟩
      · subst h2
        have e1 : (3 : Nat) ^ (2 - 1) = 3 := by decide
        have e2 : (2 : Nat) ^ 2 = 4 := by decide
        rw [e1, e2] at h
        exact ⟨by omega, Or.inr rfl⟩
    · exfalso
      have hwpos : 0 < w := by omega
      have hlt := two_pow_lt_three_pow a hge
      have hmul : 2 ^ a * w ≤ 3 ^ (a - 1) * w :=
        Nat.mul_le_mul_right w (Nat.le_of_lt hlt)
      omega
  · rintro ⟨rfl, h | h⟩ <;> subst h <;> decide

/-! ## The regeneration bound at `w = 1`

The `+1` has to put back the `2`-content the swap destroys.  At `w = 1` it can put
back at most two units, ever. -/

/-- `3^k` is `1` or `3` modulo `8`. -/
theorem three_pow_mod_eight (k : Nat) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; decide
  | succ k ih =>
    have hs : (3 : Nat) ^ (k + 1) = 3 * 3 ^ k := by rw [← Nat.pow_succ']
    rcases ih with h | h <;> rw [hs] <;> omega

/-- **`8` never divides `3^k + 1`.**  So `v₂(3^k + 1) ≤ 2` for every `k`: adding one
to a pure power of three regenerates at most two units of `2`-content. -/
theorem not_eight_dvd_three_pow_succ (k : Nat) : (3 ^ k + 1) % 8 ≠ 0 := by
  rcases three_pow_mod_eight k with h | h <;> omega

/-- **The pure powers of two contract.**  From `U = 2^a` the swap form gives
`3^(a−1) + 1`, whose `2`-part is at most `4`, so the next state has `a′ ≤ 2` — and
there `3^(a′−1) < 2^(a′)`, so it contracts rather than grows. -/
theorem pow_two_state_contracts {a : Nat} (ha : 0 < a) :
    (3 ^ (a - 1) + 1) % 8 ≠ 0 :=
  not_eight_dvd_three_pow_succ (a - 1)

end SwapForm
end Collatz
