import Collatz.Basic

/-!
Lean notes for Riho Terras,
"A stopping time problem on the positive integers",
Acta Arithmetica 30 (1976), 241--252.

Terras introduced the accelerated 3x+1 map
`T(n) = (3n+1)/2` for odd `n` and `T(n) = n/2` for even `n`
(the same accelerated map recorded in `Collatz.Papers.Lagarias2003Bibliography`)
and defined the *stopping time* `σ(n)` as the least `k ≥ 1` with `T^k(n) < n`.
His celebrated result is that the set of positive integers with a finite
stopping time has natural density `1`.

The density theorem is recorded below as a proposition, not as a theorem.
The stopping-time predicate, a bounded stopping-time value function, and a
number of finite computations are checked by Lean.

Source: Acta Arith. 30 (1976), 241--252; see also the MathWorld entry
"Collatz Problem" and Lagarias's annotated bibliography (arXiv:math/0309224).
A finer density-existence result appears in Terras, "On the existence of a
density", Acta Arith. 35 (1979), 101--102.
-/

open Classical

namespace Collatz.Papers.Terras1976

/-- The accelerated 3x+1 map `T(n) = n/2` (even), `(3n+1)/2` (odd). -/
def acceleratedStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Iteration of the accelerated map: `acceleratedOrbit k n = T^k(n)`. -/
def acceleratedOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => acceleratedOrbit k (acceleratedStep n)

/-- Terras's stopping-time predicate: `n` has a finite stopping time when some
    iterate of `T` drops strictly below the starting value `n`. -/
def hasFiniteStoppingTime (n : Nat) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ acceleratedOrbit k n < n

/-- Number of indices `i ∈ [1, N]` satisfying `p`, given decidability of `p`.
    `open Classical` supplies the low-priority `propDecidable` instance, so the
    unbounded stopping-time predicate is decidable for this counting term. -/
def countUpTo (p : Nat → Prop) [∀ a, Decidable (p a)] (N : Nat) : Nat :=
  match N with
  | 0 => 0
  | n + 1 => countUpTo p n + if p (n + 1) then 1 else 0

/-- Terras (1976), main result (recorded, not proved): the set of positive
    integers with a finite stopping time has natural density `1`. -/
def terrasDensityOne : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (countUpTo hasFiniteStoppingTime N : Rat)

/-- Least `k ∈ [1, B]` with `T^k(n) < n`, scanning ascending; `0` if none in
    range. When nonzero this is the true stopping time provided it lies in range. -/
def stoppingTimeIn (n : Nat) : Nat → Nat
  | 0 => 0
  | B + 1 =>
    let prev := stoppingTimeIn n B
    if prev ≠ 0 then prev
    else if acceleratedOrbit (B + 1) n < n then B + 1
    else 0

/-- Zero iterations leave an accelerated state unchanged. -/
@[simp] theorem acceleratedOrbit_zero_steps (n : Nat) : acceleratedOrbit 0 n = n := rfl

/-- One more accelerated iteration applies `acceleratedStep` first. -/
@[simp] theorem acceleratedOrbit_succ_steps (k n : Nat) :
    acceleratedOrbit (k + 1) n = acceleratedOrbit k (acceleratedStep n) := rfl

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_one : acceleratedStep 1 = 2 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_two : acceleratedStep 2 = 1 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_three : acceleratedStep 3 = 5 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_four : acceleratedStep 4 = 2 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_five : acceleratedStep 5 = 8 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_seven : acceleratedStep 7 = 11 := by simp [acceleratedStep]

/-- A small checked computation for the accelerated map. -/
@[simp] theorem acceleratedStep_eight : acceleratedStep 8 = 4 := by simp [acceleratedStep]

/-- Every even `n ≥ 2` drops below itself after a single accelerated step. -/
theorem hasFiniteStoppingTime_of_even (n : Nat) (hn : 0 < n) (heven : n % 2 = 0) :
    hasFiniteStoppingTime n := by
  refine ⟨1, ⟨by omega, ?_⟩⟩
  simp only [acceleratedOrbit_succ_steps, acceleratedOrbit_zero_steps, acceleratedStep, heven,
    if_pos]
  exact Nat.div_lt_self hn (by omega)

/-- The input `2` has a finite stopping time. -/
theorem hasFiniteStoppingTime_two : hasFiniteStoppingTime 2 := by
  refine ⟨1, ⟨by omega, ?_⟩⟩
  simp

/-- The input `3` has a finite stopping time (`σ(3) = 4`). -/
theorem hasFiniteStoppingTime_three : hasFiniteStoppingTime 3 := by
  refine ⟨4, ⟨by omega, ?_⟩⟩
  decide

/-- The input `4` has a finite stopping time. -/
theorem hasFiniteStoppingTime_four : hasFiniteStoppingTime 4 := by
  refine ⟨1, ⟨by omega, ?_⟩⟩
  simp

/-- The input `5` has a finite stopping time (`σ(5) = 2`). -/
theorem hasFiniteStoppingTime_five : hasFiniteStoppingTime 5 := by
  refine ⟨2, ⟨by omega, ?_⟩⟩
  decide

/-- The input `6` has a finite stopping time. -/
theorem hasFiniteStoppingTime_six : hasFiniteStoppingTime 6 :=
  hasFiniteStoppingTime_of_even 6 (by omega) (by decide)

/-- The input `7` has a finite stopping time (`σ(7) = 7`). -/
theorem hasFiniteStoppingTime_seven : hasFiniteStoppingTime 7 := by
  refine ⟨7, ⟨by omega, ?_⟩⟩
  decide

/-- The input `8` has a finite stopping time. -/
theorem hasFiniteStoppingTime_eight : hasFiniteStoppingTime 8 :=
  hasFiniteStoppingTime_of_even 8 (by omega) (by decide)

/-- The input `16` has a finite stopping time. -/
theorem hasFiniteStoppingTime_sixteen : hasFiniteStoppingTime 16 :=
  hasFiniteStoppingTime_of_even 16 (by omega) (by decide)

/-- The stopping time of `2` is `1`. -/
theorem stoppingTimeIn_two : stoppingTimeIn 2 1 = 1 := by decide

/-- The stopping time of `4` is `1`. -/
theorem stoppingTimeIn_four : stoppingTimeIn 4 1 = 1 := by decide

/-- The stopping time of `3` is `4`. -/
theorem stoppingTimeIn_three : stoppingTimeIn 3 4 = 4 := by decide

/-- The stopping time of `5` is `2`. -/
theorem stoppingTimeIn_five : stoppingTimeIn 5 2 = 2 := by decide

/-- The stopping time of `7` is `7`. -/
theorem stoppingTimeIn_seven : stoppingTimeIn 7 7 = 7 := by decide

end Collatz.Papers.Terras1976
