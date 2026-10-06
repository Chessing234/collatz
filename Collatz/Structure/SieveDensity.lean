import Collatz.Structure.Obstruction

/-!
# Finite sieve counts and a persistent obstruction

`Obstruction.sieve_never_clears` proves that at every level k the residue
`2^k−1` survives. This file gives kernel-checked counts at selected levels:

| level k | survivors | total classes |
|---|---|---|
| 4 | 3 | 16 |
| 6 | 8 | 64 |
| 8 | 19 | 256 |
| 10 | 64 | 1024 |

The survivor count increases and the proportion decreases across these four
selected levels. Those finite comparisons do not prove strict monotonicity at
every level, an unbounded survivor count, or a limiting density. In particular,
the separate geometric heavy-residue bound in `Density` should not be confused
with the finite comparisons below.

The coherent obstruction tower proves that no finite level empties this sieve.
It does not exhibit a positive integer which fails Collatz: the residues
`2^k−1` describe the 2-adic integer −1, and the positive representative changes
with k. A finite sieve's persistent obstruction does not rule out an argument
using additional orbit information or an unbounded, input-dependent horizon.

Independent counts through level 16 are recorded in
`Research/FirstLightPeriodicityProbe.json` for the coefficient-prefix test.
Identifying predicates requires a proof; matching counts alone is not one.
-/

namespace Collatz
namespace SieveDensity

open Congruence

/-- The number of residues modulo `2 ^ k` that survive the sieve to level `k`. -/
def survivorCount (k : Nat) : Nat :=
  ((List.range (2 ^ k)).filter (fun r => survives k r)).length

/-! ## The counts, by kernel evaluation -/

set_option maxRecDepth 100000 in
theorem survivorCount_four : survivorCount 4 = 3 := by decide

set_option maxRecDepth 100000 in
theorem survivorCount_six : survivorCount 6 = 8 := by decide

set_option maxRecDepth 100000 in
theorem survivorCount_eight : survivorCount 8 = 19 := by decide

set_option maxRecDepth 100000 in
theorem survivorCount_ten : survivorCount 10 = 64 := by decide

/-! ## The count never reaches zero -/

/-- The obstruction class always survives, so the count is at least one. -/
theorem one_le_survivorCount (k : Nat) : 1 ≤ survivorCount k := by
  obtain ⟨r, hlt, hs⟩ := Obstruction.sieve_never_clears k
  have hmem : r ∈ (List.range (2 ^ k)).filter (fun r => survives k r) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
    simpa using hs
  have := List.length_pos_of_mem hmem
  rw [survivorCount]
  omega

/-- The count never exceeds the modulus, so the density is a genuine fraction. -/
theorem survivorCount_le (k : Nat) : survivorCount k ≤ 2 ^ k := by
  rw [survivorCount]
  have := List.length_filter_le (fun r => survives k r) (List.range (2 ^ k))
  simpa using this

/-! ## The sieve is nested, and its obstruction is one coherent tower -/

/-- **The sieve is nested.**  Surviving to a deeper level implies surviving to
every shallower one, after reduction.  So the surviving sets form a decreasing
chain of residue classes, and "refining the sieve" is literally a refinement. -/
theorem survives_mono {j i r : Nat} (hij : i ≤ j) (h : survives j r = true) :
    survives i (r % 2 ^ i) = true := by
  refine survives_of_not_descends (fun l hl => ?_)
  have hdvd : (2:Nat) ^ l ∣ 2 ^ i := Arith.two_pow_dvd_two_pow hl
  have hmod : r % 2 ^ i % 2 ^ l = r % 2 ^ l := Nat.mod_mod_of_dvd r hdvd
  rw [hmod]
  exact not_descends_of_survives h (by omega)

/-- The obstruction class at level `k + 1` reduces to the obstruction class at
level `k`. -/
theorem obstruction_coherent (k : Nat) : (2 ^ (k + 1) - 1) % 2 ^ k = 2 ^ k - 1 := by
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  have hsplit : (2:Nat) ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by
    rw [Arith.two_pow_succ]
    omega
  rw [hsplit, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- The obstruction class survives, named explicitly rather than existentially
as in `Obstruction.sieve_never_clears`. -/
theorem survives_two_pow_sub_one (k : Nat) : survives k (2 ^ k - 1) = true := by
  refine survives_of_not_descends (fun i hi => ?_)
  cases i with
  | zero => exact Obstruction.not_descends_zero _
  | succ i => exact Obstruction.not_descends_two_pow_sub_one_at (by omega) (by omega)

/-- **The obstruction is a single coherent tower.**  For every level there is a
surviving residue, the residues at consecutive levels agree under reduction, and
so they specify one 2-adic integer that survives at every level at once.

This is the strongest form of `Obstruction.sieve_never_clears`.  The sieve does
not fail level by level for unrelated reasons; it fails at every level for the
same reason, and that reason is a single object — the 2-adic integer `−1`.  No
finite level can clear it, because the tower is coherent by construction. -/
theorem coherent_tower (k : Nat) :
    survives k (2 ^ k - 1) = true ∧
    (2 ^ (k + 1) - 1) % 2 ^ k = 2 ^ k - 1 ∧
    survives (k + 1) (2 ^ (k + 1) - 1) = true := by
  exact ⟨survives_two_pow_sub_one k, obstruction_coherent k,
    survives_two_pow_sub_one (k + 1)⟩

/-- Reduction really does map the tower onto itself, via the nesting lemma:
the deeper survivor reduces to the shallower one. -/
theorem tower_reduces (k : Nat) :
    survives k ((2 ^ (k + 1) - 1) % 2 ^ k) = true :=
  survives_mono (Nat.le_succ k) (coherent_tower k).2.2

/-! ## The two trends -/

/-- The count rises across the four explicitly checked levels. -/
theorem survivorCount_increasing :
    survivorCount 4 < survivorCount 6 ∧
    survivorCount 6 < survivorCount 8 ∧
    survivorCount 8 < survivorCount 10 := by
  rw [survivorCount_four, survivorCount_six, survivorCount_eight, survivorCount_ten]
  omega

/-- The proportion falls across the four explicitly checked levels,
expressed by integer cross multiplication. -/
theorem density_decreasing :
    survivorCount 6 * 2 ^ 4 < survivorCount 4 * 2 ^ 6 ∧
    survivorCount 8 * 2 ^ 6 < survivorCount 6 * 2 ^ 8 ∧
    survivorCount 10 * 2 ^ 8 < survivorCount 8 * 2 ^ 10 := by
  rw [survivorCount_four, survivorCount_six, survivorCount_eight, survivorCount_ten]
  decide

/-- Every level has at least one survivor, together with the proved finite
count comparisons at levels 4, 6, 8, and 10. The name is historical: the
statement does not assert unbounded growth or monotonicity at all levels. -/
theorem sieve_proliferates :
    (∀ k : Nat, 1 ≤ survivorCount k) ∧
    survivorCount 4 < survivorCount 6 ∧
    survivorCount 6 < survivorCount 8 ∧
    survivorCount 8 < survivorCount 10 ∧
    survivorCount 10 * 2 ^ 8 < survivorCount 8 * 2 ^ 10 :=
  ⟨one_le_survivorCount,
   survivorCount_increasing.1,
   survivorCount_increasing.2.1,
   survivorCount_increasing.2.2,
   density_decreasing.2.2⟩

end SieveDensity
end Collatz
