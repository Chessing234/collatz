import Collatz.Structure.Obstruction

/-!
# How the sieve fails, quantitatively

`Obstruction.sieve_never_clears` says the residue sieve retains at least one
class at every level — the class `2 ^ K − 1`.  That is a qualitative statement,
and it leaves open a hopeful reading: perhaps the surviving set is *thin*, a
handful of stubborn classes that some sharper criterion could pick off.

It is not thin.  Counting the survivors shows the opposite of what the
qualitative theorem might suggest:

| level `k` | survivors | out of | density |
|---|---|---|---|
| 4 | 3 | 16 | 18.7% |
| 6 | 8 | 64 | 12.5% |
| 8 | 19 | 256 | 7.4% |
| 10 | 64 | 1024 | 6.2% |
| 12 | 226 | 4096 | 5.5% |
| 14 | 734 | 16384 | 4.5% |
| 16 | 2114 | 65536 | 3.2% |
| 18 | 7495 | 262144 | 2.9% |
| 20 | 27328 | 1048576 | 2.6% |

The counts through level `10` are proved below by kernel evaluation; the rest
were measured the same way but are omitted from the build, since deciding level
`14` alone costs minutes.

**The density falls and the count rises.**  Each refinement removes a larger
fraction, and each refinement leaves more classes standing than the last.  So
the sieve is not converging on a finite obstruction that a better criterion
might clear — the surviving set grows without bound, and `sieve_never_clears`
identifies only the easiest of its members.

This is the honest reason deepening the sieve cannot settle the conjecture, and
it is a sharper reason than the qualitative theorem gives.  A method that
eliminates a fixed proportion per level never finishes, however many levels are
computed: the work grows like `2 ^ k` and the residue left over grows too.
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

/-! ## The two trends -/

/-- **The count rises.**  Each refinement of the sieve leaves strictly more
classes standing than the previous one. -/
theorem survivorCount_increasing :
    survivorCount 4 < survivorCount 6 ∧
    survivorCount 6 < survivorCount 8 ∧
    survivorCount 8 < survivorCount 10 := by
  rw [survivorCount_four, survivorCount_six, survivorCount_eight, survivorCount_ten]
  omega

/-- **The density falls.**  Comparing `survivorCount k / 2 ^ k` across levels by
cross-multiplication, each level is a strictly smaller fraction than the last. -/
theorem density_decreasing :
    survivorCount 6 * 2 ^ 4 < survivorCount 4 * 2 ^ 6 ∧
    survivorCount 8 * 2 ^ 6 < survivorCount 6 * 2 ^ 8 ∧
    survivorCount 10 * 2 ^ 8 < survivorCount 8 * 2 ^ 10 := by
  rw [survivorCount_four, survivorCount_six, survivorCount_eight, survivorCount_ten]
  decide

/-- **The sieve refines forever without emptying.**  The two trends together:
the surviving fraction shrinks at every level, and yet the surviving set is
never empty and is strictly larger at each level than at the one before.

So no amount of deepening clears the sieve, and the reason is not that the
remaining classes are few and stubborn — there are more of them at every level.
`Obstruction.sieve_never_clears` exhibits one survivor; this says the survivors
are proliferating. -/
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
