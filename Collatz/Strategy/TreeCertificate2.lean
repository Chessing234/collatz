import Collatz.Strategy.TreeBranching

/-!
# Certificate tables for the exponent-`2/3` tree count

**GENERATED FILE — do not edit by hand.**  Produced by
`scripts/tree_certificate2.py`; rerun the script to regenerate.

Parent classes are residues `r` modulo `243` prime to `3` (162 classes); a
child's residue modulo `81` is `childRes r v = ((2 ^ v * r) % 243 - 1) / 3`.
The tables `A`, `B` satisfy the `324` inequalities of the absolute-bound
double induction at ratio `λ = 8 / 5` (`certF`, `certH`), the lift bound
`amin_le`, and the base-case bound `base_bound` with `K = 1000000000`.

Script report: growth factor of the map at `λ = 8/5` ≈ `1.02029`; minimum
slack `RHS − LHS` over the `F`-inequalities `46195592038632`, over the `H`-inequalities
`17930536679117363200` (units: scaled by `8 ^ 18`, resp. `8 ^ 18 · 25`).
-/

namespace Collatz
namespace TreeCertificate2

open Collatz.Sum

/-- The `F`-table, indexed by `r < 243` (`0` at `r % 3 = 0`). -/
def Atab : List Nat := [
  0, 1760, 2817, 0, 1405, 1642, 0, 739, 2249, 0, 2627, 2181, 0, 2417, 1182, 0, 729, 3019, 0,
  1648, 4203, 0, 2024, 839, 0, 556, 3868, 0, 1892, 2325, 0, 1158, 1166, 0, 567, 1507, 0, 1909,
  2638, 0, 1930, 1207, 0, 904, 3238, 0, 1343, 3007, 0, 1769, 890, 0, 575, 2208, 0, 1393, 3028,
  0, 948, 1643, 0, 687, 1853, 0, 1866, 2300, 0, 1693, 908, 0, 746, 4173, 0, 1255, 3055, 0, 3138,
  898, 0, 490, 3089, 0, 1931, 2503, 0, 1190, 1446, 0, 758, 1985, 0, 2510, 2149, 0, 2714, 1403,
  0, 734, 2830, 0, 1425, 3703, 0, 2689, 920, 0, 546, 5501, 0, 1941, 2230, 0, 1057, 1295, 0, 550,
  1517, 0, 2629, 2236, 0, 2597, 1100, 0, 1026, 3565, 0, 1363, 2986, 0, 1887, 1030, 0, 524, 2709,
  0, 1453, 3593, 0, 942, 1193, 0, 754, 2031, 0, 1879, 2009, 0, 1380, 871, 0, 1027, 5020, 0,
  1437, 3567, 0, 2608, 784, 0, 561, 5101, 0, 1564, 3090, 0, 1241, 1568, 0, 877, 1904, 0, 2314,
  2355, 0, 3438, 1213, 0, 809, 3116, 0, 1398, 4016, 0, 2228, 852, 0, 644, 4342, 0, 2245, 2254,
  0, 1269, 1174, 0, 544, 1724, 0, 2229, 2280, 0, 3188, 977, 0, 980, 4302, 0, 1472, 3316, 0,
  1947, 873, 0, 532, 2500, 0, 1408, 3107, 0, 1077, 1393, 0, 611, 1692, 0, 2072, 2142, 0, 1562,
  880, 0, 870, 4170, 0, 1338, 4207, 0, 2606, 836, 0, 522, 4155]

def A (r : Nat) : Nat := Atab.getD r 0

/-- The `H`-table, indexed by `r < 243` (`0` at `r % 3 = 0`). -/
def Btab : List Nat := [
  0, 3493, 5589, 0, 2788, 3257, 0, 1466, 4461, 0, 5211, 4328, 0, 4796, 2347, 0, 1446, 5990, 0,
  3271, 8338, 0, 4015, 1666, 0, 1104, 7673, 0, 3755, 4613, 0, 2298, 2314, 0, 1126, 2990, 0,
  3788, 5233, 0, 3829, 2394, 0, 1793, 6425, 0, 2665, 5966, 0, 3509, 1767, 0, 1140, 4382, 0,
  2765, 6008, 0, 1881, 3260, 0, 1364, 3677, 0, 3702, 4563, 0, 3358, 1802, 0, 1480, 8279, 0,
  2491, 6062, 0, 6225, 1782, 0, 973, 6127, 0, 3831, 4966, 0, 2361, 2870, 0, 1504, 3939, 0, 4980,
  4265, 0, 5384, 2784, 0, 1456, 5615, 0, 2827, 7347, 0, 5334, 1825, 0, 1083, 10914, 0, 3852,
  4424, 0, 2098, 2570, 0, 1091, 3009, 0, 5216, 4437, 0, 5153, 2183, 0, 2035, 7072, 0, 2705,
  5924, 0, 3744, 2044, 0, 1041, 5373, 0, 2883, 7128, 0, 1868, 2368, 0, 1496, 4030, 0, 3728,
  3986, 0, 2738, 1728, 0, 2037, 9960, 0, 2852, 7077, 0, 5174, 1557, 0, 1114, 10120, 0, 3103,
  6130, 0, 2462, 3112, 0, 1740, 3779, 0, 4592, 4673, 0, 6821, 2407, 0, 1606, 6182, 0, 2773,
  7968, 0, 4420, 1690, 0, 1277, 8614, 0, 4455, 4472, 0, 2519, 2330, 0, 1080, 3421, 0, 4423,
  4524, 0, 6325, 1939, 0, 1945, 8535, 0, 2920, 6579, 0, 3864, 1733, 0, 1056, 4960, 0, 2795,
  6164, 0, 2138, 2764, 0, 1212, 3358, 0, 4112, 4249, 0, 3100, 1747, 0, 1727, 8272, 0, 2656,
  8346, 0, 5170, 1660, 0, 1037, 8244]

def B (r : Nat) : Nat := Btab.getD r 0

/-- The minimum of `A` over the three lifts of `c < 81` to `r < 243`. -/
def Amin (c : Nat) : Nat := min (A c) (min (A (c + 81)) (A (c + 162)))

def Bmin (c : Nat) : Nat := min (B c) (min (B (c + 81)) (B (c + 162)))

def v0R (r : Nat) : Nat := if r % 3 = 1 then 2 else 1

def phaseR (r : Nat) : Nat :=
  let b := 2 ^ v0R r * r % 9
  if b = 1 then 0 else if b = 7 then 1 else 2

/-- `TreeBranching.fval` as a function of the residue. -/
def fvalR (r i : Nat) : Nat := v0R r + 2 * (i + (i + 2 - phaseR r) / 2)

/-- The residue mod `81` of `child a v` when `a ≡ r (mod 243)`. -/
def childRes (r v : Nat) : Nat := ((2 ^ v * r) % 243 - 1) / 3

def K : Nat := 1000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
/-- The `F`-step inequalities, one per fertile class. -/
theorem certF : ∀ r, r < 243 → r % 3 ≠ 0 →
    A r * 8 ^ 18 ≤ sumRange 6 (fun i =>
      max (5 ^ fvalR r i * 8 ^ (18 - fvalR r i) * Bmin (childRes r (fvalR r i)))
          (5 ^ (fvalR r i - 1) * 8 ^ (18 - fvalR r i + 1)
            * Amin (childRes r (fvalR r i)))) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
/-- The `H`-step inequalities, one per fertile class. -/
theorem certH : ∀ r, r < 243 → r % 3 ≠ 0 →
    B r * 8 ^ 18 * 25 ≤ sumRange 6 (fun i =>
      max (5 ^ (fvalR r i + 1) * 8 ^ (18 - fvalR r i + 1) * Bmin (childRes r (fvalR r i)))
          (5 ^ (fvalR r i - 1) * 8 ^ (18 - fvalR r i + 3)
            * Amin (childRes r (fvalR r i)))) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
/-- A class's own constant dominates the minimum over the lifts of its child residue. -/
theorem amin_le : ∀ c, c < 243 → c % 3 ≠ 0 →
    Amin (c % 81) ≤ A c ∧ Bmin (c % 81) ≤ B c := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
/-- The base case `y ≤ 22`. -/
theorem base_bound : ∀ r, r < 243 → ∀ y, y ≤ 22 →
    A r * 8 ^ y ≤ 5 ^ y * K ∧ B r * 8 ^ y ≤ 5 ^ y * K := by
  decide

end TreeCertificate2
end Collatz
