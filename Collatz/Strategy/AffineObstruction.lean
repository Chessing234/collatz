import Collatz.Strategy.AffineExact
import Collatz.Strategy.RunAlgebra

/-!
# Why the affine bound does not constrain the stopping time either

Round LXXV.18 closed the heavy-window route to `DriftSurvivors`'s reduction:
heaviness bounds the *shape* of a window, never its length, because the heavy
language is nonempty at every length (`ValuationDensity.Enum_pos`).  The next
candidate was the affine identity itself,

    2 ^ j * T^j(x) = 3 ^ (oddCount x j) * x + affineC j x        (`affine_exact`)

which bounds the orbit from above and so looked like it might force a descent.

It does not, and this file says exactly why.

## The two theorems

`no_drop_forces` extracts everything the identity gives about a window with no
descent: if `T^k(n) ≥ n` for all `k ≤ j`, then

    n * 2 ^ j  ≤  3 ^ (oddCount n j) * n + affineC j n.

`affine_vacuous_of_heavy` shows that same inequality holds **with no descent
hypothesis at all**, as soon as the window is heavy — `2 ^ j ≤ 3 ^ (oddCount n j)`
alone implies it.

So the affine identity's entire content about non-descent is: *light windows are
impossible for large `n`*.  That is the certificate (`RealizableBound`), already
in the repository.  On heavy windows the constraint is implied by heaviness and
carries nothing new — and heavy windows exist at every length.

## The obstruction, stated once

Both routes fail for the same structural reason in different clothing.  The
machinery here is **scale-free in the length**: every inequality it produces is
satisfied by taking the window heavy, and heaviness is available at every `j`.
To bound `σ(n)` against `log₂ n` one needs a statement that *forces a light
window* after a controlled number of steps, and neither the heavy-window
theorems nor the affine identity contains one.

Naming that is the point of this file.  A future proposal to bound the stopping
time from the affine identity can be checked against `affine_vacuous_of_heavy`
directly: if the proposal's inequality follows from heaviness alone, it is this
one again.
-/

namespace Collatz
namespace AffineObstruction

open AffineExact

/-- **Everything the affine identity says about a window with no descent.**  If
the orbit of `n` has not fallen below `n` by step `j`, then
`n · 2 ^ j ≤ 3 ^ a · n + affineC j n`. -/
theorem no_drop_forces (n j : Nat) (hnd : n ≤ acceleratedOrbit j n) :
    n * 2 ^ j ≤ 3 ^ oddCount n j * n + affineC j n := by
  have hid := affine_exact n j
  have hmul : 2 ^ j * n ≤ 2 ^ j * acceleratedOrbit j n :=
    Nat.mul_le_mul (Nat.le_refl _) hnd
  have hcomm : (2:Nat) ^ j * n = n * 2 ^ j := Nat.mul_comm _ _
  omega

/-- **And it is vacuous on heavy windows.**  The same inequality follows from
heaviness alone, with no hypothesis about descent — so on a heavy window
`no_drop_forces` carries no information. -/
theorem affine_vacuous_of_heavy (n j : Nat) (h : 2 ^ j ≤ 3 ^ oddCount n j) :
    n * 2 ^ j ≤ 3 ^ oddCount n j * n + affineC j n := by
  have hmul : n * 2 ^ j ≤ n * 3 ^ oddCount n j :=
    Nat.mul_le_mul (Nat.le_refl n) h
  have hcomm : n * 3 ^ oddCount n j = 3 ^ oddCount n j * n := Nat.mul_comm _ _
  omega

/-- The contrapositive, which is the certificate's shape: the affine identity
bites only when the window is **light**, and then it caps `n`. -/
theorem light_caps_start (n j : Nat) (hnd : n ≤ acceleratedOrbit j n)
    (hlight : 3 ^ oddCount n j < 2 ^ j) :
    n * (2 ^ j - 3 ^ oddCount n j) ≤ affineC j n := by
  have hforce := no_drop_forces n j hnd
  have hsub : n * (2 ^ j - 3 ^ oddCount n j) = n * 2 ^ j - n * 3 ^ oddCount n j :=
    Nat.mul_sub _ _ _
  have hcomm : n * 3 ^ oddCount n j = 3 ^ oddCount n j * n := Nat.mul_comm _ _
  have hle : n * 3 ^ oddCount n j ≤ n * 2 ^ j :=
    Nat.mul_le_mul (Nat.le_refl n) (Nat.le_of_lt hlight)
  omega

end AffineObstruction
end Collatz
