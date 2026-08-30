import Collatz.Accelerated
import Collatz.Structure.Density

/-!
# No finite density test can obstruct divergence

A divergent orbit must sustain an odd-step density above `log₃ 2 = 0.63093…`
forever — equivalently `a/e > log 2/(log 3 − log 2) = 1.70951…`, since the
accelerated map multiplies by `3/2` on an odd step and by `1/2` on an even one.
That is the whole content of the divergence half, and it invites an attack on the
density directly.

**This file shows that no *finite* version of that attack can work.**

## The saturating family

`orbit_pow_pred`: for every `i ≤ m`,

`T^i(3^k · 2^m − 1) = 3^(k+i) · 2^(m−i) − 1`.

The proof is one line of arithmetic per step: `3^k · 2^m − 1 = 2A − 1` with
`A = 3^k · 2^(m−1)`, which is odd, and `(3(2A−1)+1)/2 = 3A − 1`.

Specialised at `k = 0` this says the orbit of `2^j − 1` is
`2^j − 1, 3·2^(j−1) − 1, 9·2^(j−2) − 1, …, 3^j − 1`, whose first `j` entries are
all **odd**.  Hence `oddCount_pow_pred`:

**`oddCount (2^j − 1) j = j`.**

## What that costs the density programme

The odd-step density of `2^j − 1` over its first `j` steps is exactly `1`.  So for
every window length `j`, and every threshold `d ≤ 1` — in particular the critical
`log₃ 2` — there is an explicit positive integer whose first `j` steps have
density at least `d`.  `no_finite_density_obstruction` states it:

> A density test applied to a bounded window is passed by an actual integer, at
> any threshold, for every window length.

So a divergent orbit's density requirement is *not* violated on any finite
initial segment, and cannot be: the requirement is exceeded outright, by the
maximum possible margin, by a completely explicit family.  Any obstruction to
divergence must be genuinely infinitary — it has to use the tail, not a prefix,
and not an average over a prefix.

This is the density analogue of `NoWindowObstruction.no_finite_window_obstruction`,
which says the same for parity words, and it is sharper: there the finite windows
were merely all *realised*, here the extreme one is realised by a family one can
write down.

## The `n ≡ −1 (mod 2^k)` class, again

`2^j − 1` is the `n ≡ −1 (mod 2^k)` residue class that keeps surfacing: it holds
the record-holders for long non-dropping runs, it is the shape of the extremal
words, and it is what saturates the density here.  Whatever finally settles the
divergence half will have to say something specific about this class.
-/

namespace Collatz
namespace DensitySaturation

/-- **The closed form.**  Every iterate of `3^k · 2^m − 1` is again of that shape,
with one factor of `2` traded for a factor of `3` per step, for as many steps as
there are factors of `2` to spend. -/
theorem orbit_pow_pred : ∀ i k m : Nat, i ≤ m →
    acceleratedOrbit i (3 ^ k * 2 ^ m - 1) = 3 ^ (k + i) * 2 ^ (m - i) - 1 := by
  intro i
  induction i with
  | zero => intro k m _; simp
  | succ i ih =>
    intro k m him
    have hA : 0 < 3 ^ k * 2 ^ (m - 1) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    have h2 : (2 : Nat) ^ m = 2 ^ (m - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hsplit : 3 ^ k * 2 ^ m = 2 * (3 ^ k * 2 ^ (m - 1)) := by
      rw [h2]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h3 : (3 : Nat) ^ (k + 1) * 2 ^ (m - 1) = 3 * (3 ^ k * 2 ^ (m - 1)) := by
      rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hstep : acceleratedStep (3 ^ k * 2 ^ m - 1) = 3 ^ (k + 1) * 2 ^ (m - 1) - 1 := by
      rw [hsplit, h3]
      rw [acceleratedStep, if_neg (by omega : ¬ (2 * (3 ^ k * 2 ^ (m - 1)) - 1) % 2 = 0)]
      omega
    show acceleratedOrbit i (acceleratedStep (3 ^ k * 2 ^ m - 1)) = _
    rw [hstep, ih (k + 1) (m - 1) (by omega)]
    have e1 : k + 1 + i = k + (i + 1) := by omega
    have e2 : m - 1 - i = m - (i + 1) := by omega
    rw [e1, e2]

/-- Specialised: the orbit of `2^j − 1`. -/
theorem orbit_allOnes {i j : Nat} (h : i ≤ j) :
    acceleratedOrbit i (2 ^ j - 1) = 3 ^ i * 2 ^ (j - i) - 1 := by
  have hgen := orbit_pow_pred i 0 j h
  simpa using hgen

/-- **Every one of the first `j` steps from `2^j − 1` is odd.** -/
theorem allOnes_odd {i j : Nat} (h : i < j) :
    acceleratedOrbit i (2 ^ j - 1) % 2 = 1 := by
  rw [orbit_allOnes (Nat.le_of_lt h)]
  have h2 : (2 : Nat) ^ (j - i) = 2 ^ (j - i - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hkey : 3 ^ i * 2 ^ (j - i) = 2 * (3 ^ i * 2 ^ (j - i - 1)) := by
    rw [h2]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hp : 0 < 3 ^ i * 2 ^ (j - i - 1) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  rw [hkey]
  omega

/-- **The density is saturated: `oddCount (2^j − 1) j = j`.** -/
theorem oddCount_allOnes (j : Nat) : oddCount (2 ^ j - 1) j = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hpj : 0 < (2 : Nat) ^ j := Nat.pow_pos (by omega)
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
    have hmod : (2 ^ (j + 1) - 1) % 2 ^ j = 2 ^ j - 1 := by
      have hre : 2 ^ (j + 1) - 1 = 2 ^ j + (2 ^ j - 1) := by omega
      rw [hre, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hmono : oddCount (2 ^ (j + 1) - 1) j = oddCount (2 ^ j - 1) j := by
      rw [Density.oddCount_mod (2 ^ (j + 1) - 1) j, hmod]
    rw [Density.oddCount_succ_last, allOnes_odd (Nat.lt_succ_self j), hmono, ih]

/-- The witness is positive whenever the window is nonempty. -/
theorem allOnes_pos {j : Nat} (h : 0 < j) : 0 < 2 ^ j - 1 := by
  have h1 : (2 : Nat) ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h
  rw [Nat.pow_one] at h1
  omega

/-- **No finite density test can obstruct.**  For every window length `j` there is
a positive integer whose first `j` accelerated steps are *all* odd — density `1`,
above any threshold, in particular above the critical `log₃ 2` a divergent orbit
must sustain.  A density condition read off a bounded window therefore separates
nothing. -/
theorem no_finite_density_obstruction (j : Nat) (hj : 0 < j) :
    ∃ n : Nat, 0 < n ∧ oddCount n j = j :=
  ⟨2 ^ j - 1, allOnes_pos hj, oddCount_allOnes j⟩

/-- The same, stated against an arbitrary density threshold given as a rational
`p/q ≤ 1`: some positive integer meets it on the first `j` steps. -/
theorem density_threshold_met {j p q : Nat} (hj : 0 < j) (hpq : p ≤ q) :
    ∃ n : Nat, 0 < n ∧ p * j ≤ q * oddCount n j := by
  refine ⟨2 ^ j - 1, allOnes_pos hj, ?_⟩
  rw [oddCount_allOnes j]
  exact Nat.mul_le_mul_right j hpq

/-- **And the supply is finite.**  The saturating run ends: at step `j` the orbit
of `2^j − 1` reaches `3^j − 1`, which is even.  A positive integer can imitate the
`2`-adic integer `−1` for exactly as many steps as it has trailing `1`s, and no
more. -/
theorem allOnes_exhausts (j : Nat) :
    acceleratedOrbit j (2 ^ j - 1) = 3 ^ j - 1 := by
  have h := orbit_allOnes (Nat.le_refl j)
  simpa using h

end DensitySaturation
end Collatz
