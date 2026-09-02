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

/-! ## Is "force a light window" an independent ingredient?  No — it is the
descent question itself

Iterations 18 and 19 closed two routes and named what they lacked: a statement
*forcing a light window after a controlled number of steps*.  The natural next
move is to look for that statement separately — `G1` in a sieve-testable form.

This section shows there is nothing separate to look for.  **Descent and
lightness are the same event**, up to the `affineC` correction:

* `light_of_drop` — a drop at step `j` *forces* the window light, with **no
  hypothesis at all**.  So lightness is not an extra ingredient that descent
  needs; it is a consequence of descent.
* `drop_iff_light_and_gap` — the exact converse, with the correction made
  explicit: `T^j(n) < n` holds precisely when the window is light **and**
  `affineC j n < n · (2 ^ j − 3 ^ a)`.

`Structure.Density.accOrbit_lt_of_light` already had the useful direction (light
plus a size threshold gives a drop).  What was missing is that the implication
runs both ways, and that is what settles the question: a theorem forcing light
windows on a `log₂ n` schedule *is* a theorem forcing descent on a `log₂ n`
schedule, which is `DriftSurvivors.collatz_of_logBlock17_above`'s hypothesis.
Not a prerequisite for it — the same statement.

So the ingredient the two dead routes lacked is not a smaller lemma waiting to be
proved.  It is the target restated, and any plan that treats it as a stepping
stone is circular.  Recorded so the next round does not spend a cycle looking. -/

/-! ### Prior art, and a duplication of this repository's own work

**Added Round LXXV.29.**  `light_of_drop` is Terras's elementary inequality
`σ(n) ≥ κ(n)` — R. Terras, *A stopping time problem on the positive integers*,
Acta Arith. 30 (1976) — where `κ` is the **coefficient stopping time**, the least
`m` with `2 ^ (S_m) > 3 ^ m`, i.e. the first light index.  A drop cannot precede
the first light window; that is exactly this lemma.

`Strategy.CoefficientStopping` already proves it here, as
`no_drop_of_coeff_le` / `stoppingTime_ge_coefficient`, over abstract sequences,
and states the hard half as `CSTHard`:

> **Coefficient Stopping Time conjecture (Terras 1976, Conj. 2.9).**
> `σ(n) = κ(n)` for every `n ≥ 2`.

`light_of_drop` was written in Round LXXV.20 without checking that file, so it
duplicates it in this development's own `acceleratedOrbit` / `oddCount`
indexing.  Recording the duplication rather than deleting either: the abstract
form and the concrete instance are both used, but they should not be maintained
as if independent.

What is *not* duplicated is `drop_iff_light_and_gap`, which names the exact
obstruction to the hard half.  `cst_gap_criterion` below states it in the form
that matters: **at a light index, dropping is equivalent to the accumulator
fitting inside the gap the lightness opens.**  Terras's conjecture is the claim
that this always holds at `κ`; it is open, verified by Terras for `κ(n) < 2593`
and by this repository over its own range. -/

/-- **A drop forces a light window.**  Entirely unconditional: if the orbit of
`n` falls below `n` at step `j`, then `3 ^ a < 2 ^ j` for that window.  No
positivity is needed — at `n = 0` the hypothesis is already false. -/
theorem light_of_drop {n j : Nat} (h : acceleratedOrbit j n < n) :
    3 ^ oddCount n j < 2 ^ j := by
  have hid := affine_exact n j
  have h2 : 0 < (2:Nat) ^ j := by
    have := Nat.one_le_pow j 2 (by omega); omega
  have hlt : 2 ^ j * acceleratedOrbit j n < 2 ^ j * n :=
    Nat.mul_lt_mul_of_pos_left h h2
  have hc1 : (3:Nat) ^ oddCount n j * n = n * 3 ^ oddCount n j := Nat.mul_comm _ _
  have hc2 : (2:Nat) ^ j * n = n * 2 ^ j := Nat.mul_comm _ _
  have hfin : n * 3 ^ oddCount n j < n * 2 ^ j := by omega
  exact Nat.lt_of_mul_lt_mul_left hfin

/-- **Descent, characterised exactly.**  `T^j(n) < n` iff the window is light and
the accumulator fits inside the gap it opens.  Also unconditional: at `n = 0`
both sides are false. -/
theorem drop_iff_light_and_gap (n j : Nat) :
    acceleratedOrbit j n < n ↔
      (3 ^ oddCount n j < 2 ^ j ∧
        affineC j n < n * (2 ^ j - 3 ^ oddCount n j)) := by
  have hid := affine_exact n j
  have h2 : 0 < (2:Nat) ^ j := by
    have := Nat.one_le_pow j 2 (by omega); omega
  constructor
  · intro h
    have hlight := light_of_drop h
    refine ⟨hlight, ?_⟩
    have hlt : 2 ^ j * acceleratedOrbit j n < 2 ^ j * n :=
      Nat.mul_lt_mul_of_pos_left h h2
    have hsub : n * (2 ^ j - 3 ^ oddCount n j) = n * 2 ^ j - n * 3 ^ oddCount n j :=
      Nat.mul_sub _ _ _
    have hc1 : (3:Nat) ^ oddCount n j * n = n * 3 ^ oddCount n j := Nat.mul_comm _ _
    have hc2 : (2:Nat) ^ j * n = n * 2 ^ j := Nat.mul_comm _ _
    have hle : n * 3 ^ oddCount n j ≤ n * 2 ^ j :=
      Nat.mul_le_mul (Nat.le_refl n) (Nat.le_of_lt hlight)
    omega
  · rintro ⟨hlight, hgap⟩
    have hsub : n * (2 ^ j - 3 ^ oddCount n j) = n * 2 ^ j - n * 3 ^ oddCount n j :=
      Nat.mul_sub _ _ _
    have hc1 : (3:Nat) ^ oddCount n j * n = n * 3 ^ oddCount n j := Nat.mul_comm _ _
    have hc2 : (2:Nat) ^ j * n = n * 2 ^ j := Nat.mul_comm _ _
    have hle : n * 3 ^ oddCount n j ≤ n * 2 ^ j :=
      Nat.mul_le_mul (Nat.le_refl n) (Nat.le_of_lt hlight)
    have hlt : 2 ^ j * acceleratedOrbit j n < 2 ^ j * n := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt

/-- **The coefficient-stopping criterion, localised.**  At a light index,
dropping is equivalent to `affineC` fitting inside the gap.  Terras's
Coefficient Stopping Time conjecture is the assertion that this holds at the
first light index, for every `n ≥ 2`. -/
theorem cst_gap_criterion (n j : Nat) (hlight : 3 ^ oddCount n j < 2 ^ j) :
    acceleratedOrbit j n < n ↔ affineC j n < n * (2 ^ j - 3 ^ oddCount n j) := by
  have h := drop_iff_light_and_gap n j
  constructor
  · intro hd; exact (h.mp hd).2
  · intro hg; exact h.mpr ⟨hlight, hg⟩

end AffineObstruction
end Collatz
