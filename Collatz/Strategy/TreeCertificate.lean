import Collatz.Strategy.TreeBranching

/-!
# Certificate tables for the exponent-`1/2` tree count

**GENERATED FILE — do not edit by hand.**  Produced by
`scripts/tree_certificate.py`; rerun the script to regenerate.

Parent classes are residues `r` modulo `81` prime to `3` (54 classes); a
child's residue modulo `27` is `childRes r v = ((2 ^ v * r) % 81 - 1) / 3`.
The integer tables `A`, `B` satisfy the `108` inequalities of the two-type
lattice induction at ratio `λ = 71 / 50` with clearing exponent `V = 18`
(`certF`, `certH`), the lift bound `amin_le`, and the base-case bound
`base_bound` with scaling constant `K = 10000000000`.

Script report: Perron growth factor of the map at `λ = 71/50` ≈ `1.05174`;
minimum slack `RHS − LHS` (in the units of the inequalities, i.e. scaled by `71 ^ 18`)
over the `F`-inequalities
  `18574432880654131134599869025631880030`,
over the `H`-inequalities
  `26374433439517988438344748410310366266`.
-/

namespace Collatz
namespace TreeCertificate

open Collatz.Sum

/-- The `F`-table, indexed by `r < 81` (`0` at `r % 3 = 0`). -/
def Atab : List Nat := [
  0, 393638, 558966, 0, 301340, 308299, 0, 208197, 427903, 0, 437784, 488966, 0, 480162, 295640,
  0, 208505, 591518, 0, 360074, 621654, 0, 450138, 242494, 0, 178573, 681830, 0, 419810, 518950,
  0, 279705, 296077, 0, 181242, 387508, 0, 450833, 511306, 0, 414850, 277210, 0, 217112, 639196,
  0, 344342, 597011, 0, 416562, 253573, 0, 170770, 493180, 0, 365458, 596130, 0, 272892, 317488,
  0, 195218, 397181, 0, 420430, 491307, 0, 347310, 257365, 0, 223583, 704225, 0, 345991, 640184,
  0, 495933, 243655, 0, 171588, 589087]

/-- The `F`-constant of the class `r mod 81`. -/
def A (r : Nat) : Nat := Atab.getD r 0

/-- The `H`-table, indexed by `r < 81` (`0` at `r % 3 = 0`). -/
def Btab : List Nat := [
  0, 558966, 793732, 0, 427903, 437784, 0, 295640, 607623, 0, 621654, 694332, 0, 681830, 419810,
  0, 296077, 839956, 0, 511306, 882749, 0, 639196, 344342, 0, 253573, 968198, 0, 596130, 736910,
  0, 397181, 420430, 0, 257365, 550261, 0, 640184, 726054, 0, 589087, 393638, 0, 308299, 907659,
  0, 488966, 847756, 0, 591518, 360074, 0, 242494, 700316, 0, 518950, 846504, 0, 387508, 450833,
  0, 277210, 563998, 0, 597011, 697656, 0, 493180, 365458, 0, 317488, 1000000, 0, 491307,
  909061, 0, 704225, 345991, 0, 243655, 836504]

/-- The `H`-constant of the class `r mod 81`. -/
def B (r : Nat) : Nat := Btab.getD r 0

/-- The minimum of `A` over the three lifts of a residue `c < 27` to `r < 81`. -/
def Amin (c : Nat) : Nat := min (A c) (min (A (c + 27)) (A (c + 54)))

/-- The minimum of `B` over the three lifts of a residue `c < 27` to `r < 81`. -/
def Bmin (c : Nat) : Nat := min (B c) (min (B (c + 27)) (B (c + 54)))

/-- `TreeCount.v0` as a function of the residue. -/
def v0R (r : Nat) : Nat := if r % 3 = 1 then 2 else 1

/-- `TreeBranching.phase` as a function of the residue mod `9`. -/
def phaseR (r : Nat) : Nat :=
  let b := 2 ^ v0R r * r % 9
  if b = 1 then 0 else if b = 7 then 1 else 2

/-- `TreeBranching.fval` as a function of the residue: the `i`-th fertile valuation. -/
def fvalR (r i : Nat) : Nat := v0R r + 2 * (i + (i + 2 - phaseR r) / 2)

/-- The residue mod `27` of `child a v` when `a ≡ r (mod 81)`. -/
def childRes (r v : Nat) : Nat := ((2 ^ v * r) % 81 - 1) / 3

/-- The scaling constant of the claims `A r * 71 ^ y ≤ 50 ^ y * K * S a (2 ^ y * a)`. -/
def K : Nat := 10000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `F`-step inequalities, one per fertile class. -/
theorem certF : ∀ r, r < 81 → r % 3 ≠ 0 →
    A r * 71 ^ 18 ≤ sumRange 6 (fun i =>
      max (50 ^ fvalR r i * 71 ^ (18 - fvalR r i) * Bmin (childRes r (fvalR r i)))
          (50 ^ (fvalR r i - 1) * 71 ^ (18 - fvalR r i + 1)
            * Amin (childRes r (fvalR r i)))) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `H`-step inequalities, one per fertile class. -/
theorem certH : ∀ r, r < 81 → r % 3 ≠ 0 →
    B r * 71 ^ 18 ≤ sumRange 6 (fun i =>
      max (50 ^ (fvalR r i - 1) * 71 ^ (18 - fvalR r i + 1) * Bmin (childRes r (fvalR r i)))
          (if 3 ≤ fvalR r i then
            50 ^ (fvalR r i - 2) * 71 ^ (18 - fvalR r i + 2)
              * Amin (childRes r (fvalR r i))
          else 0)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A class's own constant dominates the minimum over the lifts of its child residue. -/
theorem amin_le : ∀ c, c < 81 → c % 3 ≠ 0 →
    Amin (c % 27) ≤ A c ∧ Bmin (c % 27) ≤ B c := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The base case `y ≤ 22`: the claims follow from `S ≥ 1` alone.  (The inductive
step starts at `y = 23`, where every child bound has slack `2 ^ (y − v) ≥ 32 ≥ 18`.) -/
theorem base_bound : ∀ r, r < 81 → ∀ y, y ≤ 22 →
    A r * 71 ^ y ≤ 50 ^ y * K ∧ B r * 71 ^ y ≤ 50 ^ y * K := by
  decide

end TreeCertificate
end Collatz
