import Collatz.Basic

/-!
# A proposed minimum-density induction needs more than coarse consistency

This is NOT the actual Syracuse law and NOT a counterexample to Collatz.
It refutes using only normalization, a positive floor, coarse projection,
and the doubling identity to justify the proposed logistic floor update.

The density on residues modulo 9 is `weight / 7`. Its minimum on units is
2/7 and its projection modulo 3 is the actual first Syracuse density.
The exact finite geometric-period transfer at residue 25 is 794/9709,
which is smaller than (2/7)/(1+3*(2/7)) = 2/13.

The finite statements below are checked by `decide`. Identifying the finite
geometric-period transfer with an infinite geometric sum is a separate
elementary grouping argument described in `Devices/MultiscaleSyracuse.md`;
no infinite probability law is formalized in this file.
-/

namespace Collatz.SyracuseFloorObstruction

def weight (r : Nat) : Nat :=
  [0, 2, 4, 0, 17, 4, 0, 2, 34][r]?.getD 0

theorem normalized : ((List.range 9).map weight).sum = 9 * 7 := by decide

theorem positive_floor : ∀ r : Fin 9,
    (r.val % 3 = 0 → weight r.val = 0) ∧
    (r.val % 3 ≠ 0 → 2 ≤ weight r.val) := by decide

theorem floor_attained : weight 1 = 2 := by decide

theorem projects_to_first : ∀ c : Fin 3, c.val ≠ 0 →
    weight c.val + weight (c.val + 3) + weight (c.val + 6) = 21 * c.val := by
  decide

theorem doubling : ∀ r : Fin 9, r.val % 3 = 1 →
    weight ((2 * r.val) % 9) = 2 * weight r.val := by decide

theorem valuation_period : 2 ^ 18 % 27 = 1 := by decide

/-- Numerator with common denominator `7 * (2^18 - 1)`. -/
def transferNumerator : Nat :=
  ((List.range 18).map (fun i =>
    let v := i + 1
    let z := (2 ^ v * 25) % 27
    if z % 3 = 1 then 3 * 2 ^ (18 - v) * weight ((z - 1) / 3) else 0)).sum

theorem transfer_exact : transferNumerator = 150066 := by decide

theorem transfer_reduced :
    transferNumerator * 9709 = 794 * (7 * (2 ^ 18 - 1)) := by decide

/-- Cross-multiplied strict failure of the proposed `2/13` lower bound. -/
theorem logistic_floor_fails :
    13 * transferNumerator < 2 * (7 * (2 ^ 18 - 1)) := by decide

end Collatz.SyracuseFloorObstruction
