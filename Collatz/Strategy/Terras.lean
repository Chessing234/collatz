import Collatz.Structure.Density
import Collatz.Strategy.Pillars

/-!
# What the density theorem buys, and what it costs

`Collatz.Structure.Density` proves that the residues obstructing `k`-step
descent — the heavy ones — form a geometrically vanishing fraction of all
residues.  This file states precisely what that does and does not settle, so the
result is not mistaken for more than it is.

**What it buys.**  For every level `k`, every light residue class descends past
a threshold (`Density.accOrbit_lt_of_light`), and the heavy classes number at
most `(243/256)^{k/5} · 2^k`.  So the obstruction to the single-pillar
formulation of Collatz is confined to a set of residues of density zero.

**What it costs.**  Nothing in that argument reaches the conjecture, and
`no_level_suffices` below explains why in the sharpest possible terms: for every
level `k` there are arbitrarily large integers whose residue is heavy at that
level.  The exceptional set is not merely nonempty, it is unbounded.  A proof of
Collatz must therefore handle integers that no fixed level of the analysis ever
reaches — which is exactly the boundary the elementary theory has never crossed.
-/

namespace Collatz
namespace Strategy

open Reach Congruence Density

/-! ## The theorem, restated -/

/-- **Terras density, integer form.**  The heavy residues at level `k` satisfy
`heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k`, i.e. their fraction among all `2 ^ k`
classes has fifth power at most `(243/256) ^ k`. -/
theorem terras_density (k : Nat) : heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k :=
  heavyCount_pow_five k

/-- Every residue is either heavy or its class eventually descends. -/
theorem heavy_or_descends (k r : Nat) :
    heavyB k r = true ∨
      ∃ M : Nat, ∀ m : Nat, M ≤ m →
        acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r :=
  heavy_or_eventually_descends k r

/-! ## Why no single level closes the problem -/

/-- The heavy residue `2 ^ k − 1` has arbitrarily large representatives, and
each keeps the same residue. -/
theorem exists_large_heavy_representative (k N : Nat) :
    ∃ n : Nat, N < n ∧ heavyB k (n % 2 ^ k) = true := by
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  refine ⟨2 ^ k * (N + 1) + (2 ^ k - 1), ?_, ?_⟩
  · have h1 : N + 1 ≤ 2 ^ k * (N + 1) := Nat.le_mul_of_pos_left _ hpow
    omega
  · have hmod : (2 ^ k * (N + 1) + (2 ^ k - 1)) % 2 ^ k = 2 ^ k - 1 := by
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    cases k with
    | zero => simp [heavyB]
    | succ m => exact heavy_two_pow_sub_one (by omega)

/-- **No level suffices.**  For every level `k` of the residue analysis there are
arbitrarily large integers whose residue is heavy at that level, so the
obstruction set is unbounded, not merely nonempty.

This is the precise sense in which the density theorem, though sharp, leaves the
conjecture untouched. -/
theorem no_level_suffices (k : Nat) :
    ∀ N : Nat, ∃ n : Nat, N < n ∧ heavyB k (n % 2 ^ k) = true :=
  fun N => exists_large_heavy_representative k N

/-- The heavy count is positive at every positive level, so the sieve of
`Collatz.Structure.Minimal` can never be driven to an empty survivor list by
increasing the modulus. -/
theorem heavyCount_never_zero {k : Nat} (hk : 0 < k) : heavyCount k ≠ 0 := by
  have := heavyCount_pos hk
  omega

/-- The two halves side by side: vanishing density, unbounded obstruction. -/
theorem density_zero_but_obstruction_unbounded {k : Nat} (hk : 0 < k) :
    (heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k) ∧
    (∀ N : Nat, ∃ n : Nat, N < n ∧ heavyB k (n % 2 ^ k) = true) :=
  ⟨terras_density k, no_level_suffices k⟩

end Strategy
end Collatz
