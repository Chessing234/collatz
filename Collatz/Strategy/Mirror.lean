import Collatz.Strategy.OneRunCycle

/-!
# The mirror world, and what it proves about this development

Replace `3n + 1` by `3n − 1` and the shift `u = x + 1` by `u = x − 1`.  Every
structural theorem in this project has an exact analogue in that world, because
every one of them is derived from the identity `2(T(x)+1) = 3(x+1)` and from
congruences — and the mirror identity `2(T(x)−1) = 3(x−1)` holds verbatim.

**But the mirror world has nontrivial cycles.**  `5 → 7 → 10 → 5` is one, so `5`
never drops there, and it is not `1`.

This file proves that, and then checks that `5` satisfies the mirror analogue of
the profile this development derives for a least never-dropper:

* `4 ∣ (m − 1)`  — the analogue of `m ≡ 3 (mod 4)`;
* `3 ∤ (m − 1)`  — the analogue of `m ≢ 2 (mod 3)`;
* the **master bound** `3 ^ j (m−1) ≤ 2 ^ j (v−1)` whenever `3 ^ j ∣ (v−1)`, at
  *every* orbit point — and with equality at `T(m)` and `T²(m)`, exactly the
  sharpness observed in `BackwardRun` and `OrbitDescent`.

## The consequence

Every theorem in this development that is proved from the shift identity and
congruences alone is **blind to the sign of the `1`**.  Such theorems hold in the
mirror world too, where a nontrivial never-dropper exists.  Therefore

**no combination of them can prove the Collatz conjecture.**

That is not a statement about effort or ingenuity; it is a statement about what
those hypotheses entail, witnessed by a model in which they all hold and the
conclusion fails.

The one thing in the development that is *not* mirror-invariant is the verified
range `m ≥ 307 200` (`VerifiedSharp`), which is a computation about `3n + 1`
specifically — in the mirror world the least never-dropper is `5`.  So any
completion of this programme must use the verified range **quantitatively**, in
the shape "every never-dropper is smaller than `B`" for an explicit `B`.
`OneRunCycle` is the first result here with that shape, and it is exactly why
that direction is the live one.
-/

namespace Collatz
namespace Mirror

/-! ## The mirror map -/

/-- The accelerated `3n − 1` map. -/
def mirrorStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n - 1) / 2

/-- Its orbit. -/
def mirrorOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => mirrorOrbit k (mirrorStep n)

theorem mirrorOrbit_succ_step (k n : Nat) :
    mirrorOrbit (k + 1) n = mirrorStep (mirrorOrbit k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [mirrorOrbit, ih, mirrorOrbit]

/-- The mirror analogue of `NeverDrops`. -/
def MirrorNeverDrops (x : Nat) : Prop := ∀ j : Nat, x ≤ mirrorOrbit j x

/-! ## Five never drops -/

/-- The orbit of `5` is the three-cycle `5 → 7 → 10 → 5`. -/
theorem orbit_five : ∀ k : Nat,
    mirrorOrbit k 5 = 5 ∨ mirrorOrbit k 5 = 7 ∨ mirrorOrbit k 5 = 10 := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [mirrorOrbit_succ_step]
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- **`5` never drops in the mirror world**, and it is not `1`. -/
theorem five_neverDrops : MirrorNeverDrops 5 := by
  intro j
  rcases orbit_five j with h | h | h <;> rw [h] <;> omega

/-- `17` is a second, independent witness (its cycle has length eleven). -/
theorem seventeen_cycles : mirrorOrbit 11 17 = 17 := by decide

/-! ## Five satisfies the whole mirror profile -/

/-- The analogue of `m ≡ 3 (mod 4)`. -/
theorem five_mod_four : (5 - 1) % 4 = 0 := by decide

/-- The analogue of `m ≢ 2 (mod 3)`. -/
theorem five_not_two_mod_three : ¬ (3 ∣ (5 - 1)) := by decide

/-- **The master bound holds at every orbit point of `5`.**  For every `j` and
every orbit index `k`, if `3 ^ j ∣ (v − 1)` then `3 ^ j (5 − 1) ≤ 2 ^ j (v − 1)`. -/
theorem five_master_bound (j k : Nat)
    (hdvd : 3 ^ j ∣ (mirrorOrbit k 5 - 1)) :
    3 ^ j * (5 - 1) ≤ 2 ^ j * (mirrorOrbit k 5 - 1) := by
  have hv := orbit_five k
  have hj : j ≤ 2 := by
    rcases Nat.lt_or_ge j 3 with h | h
    · omega
    · exfalso
      have hpow : (3:Nat) ^ 3 ≤ 3 ^ j := Arith.three_pow_le_three_pow h
      have h27 : (3:Nat) ^ 3 = 27 := by decide
      have hd : 0 < mirrorOrbit k 5 - 1 := by
        rcases hv with h1 | h1 | h1 <;> rw [h1] <;> omega
      have hle := Nat.le_of_dvd hd hdvd
      rcases hv with h1 | h1 | h1 <;> rw [h1] at hle <;> omega
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with hj0 | hj0 | hj0 <;> subst hj0 <;>
    rcases hv with h1 | h1 | h1 <;> rw [h1] at hdvd ⊢ <;> revert hdvd <;> decide

/-- Sharpness, mirrored: the bound holds with **equality** at `T(m)` and `T²(m)`,
exactly as `OrbitDescent.windows_sharp` reports for `3n + 1`. -/
theorem five_bound_sharp :
    3 ^ 1 * (5 - 1) = 2 ^ 1 * (mirrorOrbit 1 5 - 1) ∧
    3 ^ 2 * (5 - 1) = 2 ^ 2 * (mirrorOrbit 2 5 - 1) := by
  constructor <;> decide

/-! ## What this rules out -/

/-- **The impossibility statement.**  There is a number other than `1` that never
drops in the mirror world, satisfying every mirror analogue of the profile this
development proves: the congruence conditions, the master bound at every orbit
point, and its sharpness at the first two steps.

So the shift identity together with congruence reasoning — which is what all of
`OddRuns`, `RunValue`, `BackwardRun`, `ThreeAdic`, `Descent` and `OrbitDescent`
rest on — cannot separate `3n + 1` from `3n − 1`, and therefore cannot prove
Collatz on its own. -/
theorem mirror_model_of_the_profile :
    ∃ m : Nat, 1 < m ∧ MirrorNeverDrops m ∧
      (m - 1) % 4 = 0 ∧ ¬ (3 ∣ (m - 1)) ∧
      (∀ j k : Nat, 3 ^ j ∣ (mirrorOrbit k m - 1) →
        3 ^ j * (m - 1) ≤ 2 ^ j * (mirrorOrbit k m - 1)) :=
  ⟨5, by omega, five_neverDrops, five_mod_four, five_not_two_mod_three,
   fun j k h => five_master_bound j k h⟩

end Mirror
end Collatz
