import Collatz.Exploration.OrbitFloor
import Collatz.Core.Reach

/-!
# Exact time change between the two Collatz conventions

The accelerated map in this project removes exactly one forced even step
following an odd step. It is not the odd-only Syracuse map. Each accelerated
step consumes one or two standard steps. The explicit clock below identifies
all retained states, and its gaps contain just the odd expansion states.

Consequences include equality of orbit lower bounds, equality of orbit floors,
and a factor-two bound for translating a descent witness. These statements
make no assumption about convergence. They are elementary convention bridges,
not a new universal descent theorem.
-/
namespace Collatz.Exploration.TimeChange

open Reach OrbitFloor

/-- Standard steps consumed by the accelerated transition at time `j`. -/
def duration (n j : Nat) : Nat :=
  if acceleratedOrbit j n % 2 = 0 then 1 else 2

/-- Standard time at the boundary of accelerated step `j`. -/
def clock (n : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => clock n j + duration n j

@[simp] theorem clock_zero (n : Nat) : clock n 0 = 0 := rfl

@[simp] theorem clock_succ (n j : Nat) :
    clock n (j+1) = clock n j + duration n j := rfl

/-- The time change never pauses or skips more than two standard steps. -/
theorem duration_bounds (n j : Nat) :
    1 ≤ duration n j ∧ duration n j ≤ 2 := by
  unfold duration
  split <;> omega

/-- Accelerated time is at most standard time, which is at most twice it. -/
theorem clock_bounds (n j : Nat) : j ≤ clock n j ∧ clock n j ≤ 2*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [clock_succ]
    have := duration_bounds n j
    omega

/-- Every clock increment is strictly positive. -/
theorem clock_lt_succ (n j : Nat) : clock n j < clock n (j+1) := by
  rw [clock_succ]
  have := duration_bounds n j
  omega

/-- The explicit clock recovers every accelerated state in the standard orbit. -/
theorem orbit_at_clock (n j : Nat) :
    orbit (clock n j) n = acceleratedOrbit j n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [clock_succ, Nat.add_comm, orbit_add, ih]
    rw [acceleratedOrbit_succ_step]
    unfold duration
    by_cases he : acceleratedOrbit j n % 2 = 0
    · rw [if_pos he]
      exact (accStep_eq_step_of_even he).symm
    · rw [if_neg he]
      have ho : acceleratedOrbit j n % 2 = 1 := by omega
      have hp : 0 < acceleratedOrbit j n := by omega
      exact (accStep_eq_step_step_of_odd hp ho).symm

/-- The one state omitted by an odd accelerated transition is its expansion. -/
theorem orbit_inside_odd {n j : Nat}
    (ho : acceleratedOrbit j n % 2 = 1) :
    orbit (clock n j+1) n = 3*acceleratedOrbit j n+1 := by
  rw [Nat.add_comm, orbit_add, orbit_at_clock]
  exact step_odd (by omega) ho

/-- Each standard time is a retained boundary or the single omitted odd state.
The witness includes its exact time, rather than merely a state equality. -/
theorem clock_cover (n k : Nat) : ∃ j,
    (k = clock n j ∧ orbit k n = acceleratedOrbit j n) ∨
    (k = clock n j+1 ∧ acceleratedOrbit j n % 2 = 1 ∧
      orbit k n = 3*acceleratedOrbit j n+1) := by
  induction k with
  | zero => exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  | succ k ih =>
    obtain ⟨j, hj | hj⟩ := ih
    · by_cases he : acceleratedOrbit j n % 2 = 0
      · have ht : k+1 = clock n (j+1) := by
          rw [clock_succ, duration, if_pos he, hj.1]
        exact ⟨j+1, Or.inl ⟨ht, by rw [ht, orbit_at_clock]⟩⟩
      · have ho : acceleratedOrbit j n % 2 = 1 := by omega
        have ht : k+1 = clock n j+1 := by omega
        exact ⟨j, Or.inr ⟨ht, ho, by rw [ht]; exact orbit_inside_odd ho⟩⟩
    · have he : ¬ acceleratedOrbit j n % 2 = 0 := by omega
      have ht : k+1 = clock n (j+1) := by
        rw [clock_succ, duration, if_neg he]
        omega
      exact ⟨j+1, Or.inl ⟨ht, by rw [ht, orbit_at_clock]⟩⟩

/-- Both conventions have exactly the same set of lower bounds. -/
theorem lower_bounds_iff (n b : Nat) :
    (∀ k, b ≤ orbit k n) ↔ (∀ j, b ≤ acceleratedOrbit j n) := by
  constructor
  · intro h j
    rw [← orbit_at_clock]
    exact h (clock n j)
  · intro h k
    obtain ⟨j, hj | hj⟩ := clock_cover n k
    · rw [hj.2]
      exact h j
    · rw [hj.2.2]
      have := h j
      omega

/-- The standard nontrivial floor predicate transfers without any loss. -/
theorem floor_iff (m : Nat) :
    Floor m ↔ (1 < m ∧ ∀ j, m ≤ acceleratedOrbit j m) := by
  exact and_congr_right fun _ => lower_bounds_iff m m

/-- Any accelerated descent has a standard witness within twice the time. -/
theorem standard_drop_of_accelerated {n j : Nat}
    (hd : acceleratedOrbit j n < n) :
    ∃ k, j ≤ k ∧ k ≤ 2*j ∧ orbit k n < n := by
  obtain ⟨hlo, hhi⟩ := clock_bounds n j
  exact ⟨clock n j, hlo, hhi, by rw [orbit_at_clock]; exact hd⟩

/-- A standard descent supplies an accelerated descent no later than its time.
If the standard witness is an omitted expansion, its retained predecessor is
already smaller. This is why omitting expansions cannot hide a first drop. -/
theorem accelerated_drop_of_standard {n k : Nat}
    (hd : orbit k n < n) :
    ∃ j, j ≤ k ∧ acceleratedOrbit j n < n := by
  obtain ⟨j, hj | hj⟩ := clock_cover n k
  · have := (clock_bounds n j).1
    exact ⟨j, by omega, by rw [← hj.2]; exact hd⟩
  · have := (clock_bounds n j).1
    rw [hj.2.2] at hd
    exact ⟨j, by omega, by omega⟩

/-- Universal descent is the same assertion under the two conventions. -/
theorem descent_iff (n : Nat) :
    (∃ k, orbit k n < n) ↔ (∃ j, acceleratedOrbit j n < n) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, _, hj⟩ := accelerated_drop_of_standard hk
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, _, _, hk⟩ := standard_drop_of_accelerated hj
    exact ⟨k, hk⟩

/-- A standard upper bound also bounds all accelerated states. -/
theorem acc_upper_bound {n B : Nat} (h : ∀ k, orbit k n ≤ B) :
    ∀ j, acceleratedOrbit j n ≤ B := by
  intro j
  rw [← orbit_at_clock]
  exact h (clock n j)

/-- An accelerated upper bound controls omitted expansions by `3B+1`. -/
theorem standard_upper_bound {n B : Nat}
    (h : ∀ j, acceleratedOrbit j n ≤ B) : ∀ k, orbit k n ≤ 3*B+1 := by
  intro k
  obtain ⟨j, hj | hj⟩ := clock_cover n k
  · rw [hj.2]
    have := h j
    omega
  · rw [hj.2.2]
    have := h j
    omega

/-- Boundedness is also independent of the convention. -/
theorem bounded_iff (n : Nat) :
    (∃ B, ∀ k, orbit k n ≤ B) ↔ (∃ B, ∀ j, acceleratedOrbit j n ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, acc_upper_bound hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨3*B+1, standard_upper_bound hB⟩

end Collatz.Exploration.TimeChange
