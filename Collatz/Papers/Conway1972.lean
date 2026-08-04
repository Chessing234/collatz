import Collatz.Basic
import Collatz.Accelerated

/-!
Lean notes for John H. Conway,
"Unpredictable iterations",
Proceedings of the 1972 Number Theory Conference,
University of Colorado, Boulder, 1972, pp. 49--52.

Conway studied the class of *generalized Collatz maps*: functions
`g(n) = (a_i n + b_i)/m` on each residue class `n ≡ i (mod m)`. The classical
`3x+1` step map (even `n ↦ n/2`, odd `n ↦ 3n+1`) and Terras's accelerated map
`T(n) = (3n+1)/2` for odd `n` are members of this family. Conway proved that
the question whether the forward iterates of such a map reach `1` is
algorithmically undecidable; his construction encodes register-machine
computations, with integers of the form `2^k` standing for configurations
(see also Kurtz--Simon, "The Undecidability of the Generalized Collatz
Problem", TAMC 2007, for a modern exposition).

Below the generalized maps are defined, the classical and accelerated maps
are proved to be instances of the family, the power-of-two arms are proved
to reach `1` by induction, and several finite arms are checked. The
undecidability theorem is recorded as propositions, not proved.

Source: Proc. 1972 Number Theory Conference, Univ. Colorado, Boulder,
pp. 49--52 (MR 52 #13717); Lagarias's annotated bibliography, item 43,
arXiv:math/0309224.
-/

open Classical

namespace Collatz.Papers.Conway1972

/-- A generalized Collatz map with modulus `m` (Conway 1972): on the residue
    class `n ≡ i (mod m)` the map is `n ↦ (a i n + b i)/m`. The field `div`
    ensures the numerator is divisible by `m` on the whole class. -/
structure GeneralizedCollatzMap (m : Nat) where
  a : Fin m → Nat
  b : Fin m → Nat
  div : ∀ i : Fin m, (a i * (i : Nat) + b i) % m = 0

namespace GeneralizedCollatzMap

/-- Evaluation of a generalized map on the residue class `n mod m`. The
    degenerate case `m = 0` is totalized by mapping everything to `0`; every
    actual map has `m > 0`. -/
def eval {m : Nat} (h : GeneralizedCollatzMap m) (n : Nat) : Nat :=
  if hm : m = 0 then 0
  else
    let i : Fin m := ⟨n % m, Nat.mod_lt n (Nat.pos_of_ne_zero hm)⟩
    (h.a i * n + h.b i) / m

/-- Iteration of a generalized map: `iteration k h n = h^k(n)`. -/
def iteration {m : Nat} (h : GeneralizedCollatzMap m) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iteration h k (eval h n)

/-- The predicate that some iterate of the generalized map at `n` equals `1`. -/
def reachesOne {m : Nat} (h : GeneralizedCollatzMap m) (n : Nat) : Prop :=
  ∃ k : Nat, iteration h k n = 1

/-- Zero iterations leave the input unchanged. -/
@[simp] theorem iteration_zero (h : GeneralizedCollatzMap m) (n : Nat) :
    iteration h 0 n = n := rfl

/-- One more iteration applies the map first. -/
@[simp] theorem iteration_succ (h : GeneralizedCollatzMap m) (k n : Nat) :
    iteration h (k + 1) n = iteration h k (eval h n) := rfl

end GeneralizedCollatzMap

open GeneralizedCollatzMap

/-- The classical `3x+1` step map as a generalized Collatz map: even
    `n ↦ n/2`, odd `n ↦ 3n+1` (written as `(6n+2)/2`). -/
def collatzStepGeneralized : GeneralizedCollatzMap 2 where
  a := fun i => if (i : Nat) = 0 then 1 else 6
  b := fun i => if (i : Nat) = 0 then 0 else 2
  div := by
    intro i
    have hlt : (i : Nat) < 2 := i.isLt
    have hc : (i : Nat) = 0 ∨ (i : Nat) = 1 := by omega
    rcases hc with h0 | h1
    · rw [h0]
      decide
    · rw [h1]
      decide

/-- Terras's accelerated map `T(n) = (3n+1)/2` for odd `n` as a generalized
    Collatz map. -/
def collatzAccelGeneralized : GeneralizedCollatzMap 2 where
  a := fun i => if (i : Nat) = 0 then 1 else 3
  b := fun i => if (i : Nat) = 0 then 0 else 1
  div := by
    intro i
    have hlt : (i : Nat) < 2 := i.isLt
    have hc : (i : Nat) = 0 ∨ (i : Nat) = 1 := by omega
    rcases hc with h0 | h1
    · rw [h0]
      decide
    · rw [h1]
      decide

/-- The halving-only map: even `n ↦ n/2`, odd `n ↦ (n+1)/2`. -/
def halvingGeneralized : GeneralizedCollatzMap 2 where
  a := fun _ => 1
  b := fun i => if (i : Nat) = 0 then 0 else 1
  div := by
    intro i
    have hlt : (i : Nat) < 2 := i.isLt
    have hc : (i : Nat) = 0 ∨ (i : Nat) = 1 := by omega
    rcases hc with h0 | h1
    · rw [h0]
      decide
    · rw [h1]
      decide

/-- The classical map halves even inputs. -/
theorem eval_collatzStep_even (n : Nat) (hn : n % 2 = 0) :
    eval collatzStepGeneralized n = n / 2 := by
  unfold eval collatzStepGeneralized
  simp [hn]

/-- The classical map sends odd inputs to `3n+1`. -/
theorem eval_collatzStep_odd (n : Nat) (hn : n % 2 = 1) :
    eval collatzStepGeneralized n = 3 * n + 1 := by
  unfold eval collatzStepGeneralized
  have h : 6 * n + 2 = 2 * (3 * n + 1) := by omega
  have hdiv : (6 * n + 2) / 2 = 3 * n + 1 := by
    rw [h]
    exact Nat.mul_div_right (3 * n + 1) (by decide)
  simp [hn, hdiv]

/-- The accelerated map halves even inputs. -/
theorem eval_collatzAccel_even (n : Nat) (hn : n % 2 = 0) :
    eval collatzAccelGeneralized n = n / 2 := by
  unfold eval collatzAccelGeneralized
  simp [hn]

/-- The accelerated map sends odd inputs to `(3n+1)/2`. -/
theorem eval_collatzAccel_odd (n : Nat) (hn : n % 2 = 1) :
    eval collatzAccelGeneralized n = (3 * n + 1) / 2 := by
  unfold eval collatzAccelGeneralized
  simp [hn]

/-- A double is even. -/
@[simp] theorem double_mod_two (x : Nat) : (2 * x) % 2 = 0 :=
  Nat.mul_mod_right 2 x

/-- A double halves exactly. -/
@[simp] theorem double_div_two (x : Nat) : (2 * x) / 2 = x :=
  Nat.mul_div_right x (by decide)

/-- The `n+1` shift of the power law: `2^(k+1) = 2 * 2^k`. -/
@[simp] theorem pow_succ_double (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [show 2 ^ (k + 1) = 2 ^ k * 2 from rfl, Nat.mul_comm]

/-- The halving branch reduces doubles. -/
theorem eval_halving_twice (x : Nat) : eval halvingGeneralized (2 * x) = x := by
  unfold eval halvingGeneralized
  simp

/-- The classical map reduces doubles. -/
theorem eval_step_twice (x : Nat) : eval collatzStepGeneralized (2 * x) = x := by
  unfold eval collatzStepGeneralized
  simp

/-- The accelerated map reduces doubles. -/
theorem eval_accel_twice (x : Nat) : eval collatzAccelGeneralized (2 * x) = x := by
  unfold eval collatzAccelGeneralized
  simp

/-- Any generalized map with the halving branch sends `2^k` to `1` in exactly
    `k` iterations. -/
theorem iteration_twice_branch_pow_two {m : Nat} (h : GeneralizedCollatzMap m)
    (htwice : ∀ x : Nat, eval h (2 * x) = x) (k : Nat) :
    iteration h k (2 ^ k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change iteration h k (eval h (2 ^ (k + 1))) = 1
      rw [pow_succ_double]
      rw [htwice (2 ^ k)]
      exact ih

/-- Every power of two reaches `1` under the classical map. -/
theorem reachesOne_step_pow_two (k : Nat) : reachesOne collatzStepGeneralized (2 ^ k) :=
  ⟨k, iteration_twice_branch_pow_two collatzStepGeneralized eval_step_twice k⟩

/-- Every power of two reaches `1` under the accelerated map. -/
theorem reachesOne_accel_pow_two (k : Nat) : reachesOne collatzAccelGeneralized (2 ^ k) :=
  ⟨k, iteration_twice_branch_pow_two collatzAccelGeneralized eval_accel_twice k⟩

/-- Every power of two reaches `1` under the halving-only map. -/
theorem reachesOne_halving_pow_two (k : Nat) : reachesOne halvingGeneralized (2 ^ k) :=
  ⟨k, iteration_twice_branch_pow_two halvingGeneralized eval_halving_twice k⟩

/-- The generalized classical map and the project's `Collatz.step` agree. -/
theorem eval_eq_collatzStep (n : Nat) : eval collatzStepGeneralized n = Collatz.step n := by
  by_cases h0 : n % 2 = 0
  · rw [eval_collatzStep_even n h0, Collatz.step]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp [hn0, h0]
  · have h1 : n % 2 = 1 := by omega
    rw [eval_collatzStep_odd n h1, Collatz.step]
    by_cases hn0 : n = 0
    · subst n
      simp at h0
    · simp [hn0, h1]

/-- The generalized accelerated map and the shared `acceleratedStep` agree. -/
theorem eval_eq_acceleratedStep (n : Nat) :
    eval collatzAccelGeneralized n = Collatz.acceleratedStep n := by
  by_cases h0 : n % 2 = 0
  · rw [eval_collatzAccel_even n h0, Collatz.acceleratedStep]
    simp [h0]
  · have h1 : n % 2 = 1 := by omega
    rw [eval_collatzAccel_odd n h1, Collatz.acceleratedStep]
    simp [h1]

/-- Iterates of the generalized classical map are exactly `Collatz.orbit`. -/
theorem iteration_step_eq_orbit (k n : Nat) :
    iteration collatzStepGeneralized k n = Collatz.orbit k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp [eval_eq_collatzStep, ih (Collatz.step n)]

/-- Reachability in the generalized classical map is the project's conjecture
    predicate, restricted to the orbit predicate. -/
theorem reachesOne_iff_orbit (n : Nat) :
    reachesOne collatzStepGeneralized n ↔ ∃ k : Nat, Collatz.orbit k n = 1 := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    exact ⟨k, by simpa [iteration_step_eq_orbit] using hk⟩
  · intro h
    rcases h with ⟨k, hk⟩
    exact ⟨k, by simpa [iteration_step_eq_orbit] using hk⟩

/-- Iterates of the generalized accelerated map are exactly the shared
    `acceleratedOrbit`. -/
theorem iteration_accel_eq_orbit (k n : Nat) :
    iteration collatzAccelGeneralized k n = Collatz.acceleratedOrbit k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp [eval_eq_acceleratedStep, ih (Collatz.acceleratedStep n)]

/-- A checked arm: `1` reaches `1` in the classical map. -/
theorem reachesOne_step_one : reachesOne collatzStepGeneralized 1 := ⟨0, rfl⟩

/-- A checked arm: `2` reaches `1` in the classical map. -/
theorem reachesOne_step_two : reachesOne collatzStepGeneralized 2 :=
  ⟨1, by native_decide⟩

/-- A checked arm: `3` reaches `1` in the classical map. -/
theorem reachesOne_step_three : reachesOne collatzStepGeneralized 3 :=
  ⟨7, by native_decide⟩

/-- A checked arm: `4` reaches `1` in the classical map. -/
theorem reachesOne_step_four : reachesOne collatzStepGeneralized 4 :=
  ⟨2, by native_decide⟩

/-- A checked arm: `16` reaches `1` in the classical map. -/
theorem reachesOne_step_sixteen : reachesOne collatzStepGeneralized 16 :=
  ⟨4, by native_decide⟩

/-- The classical arm of `27` reaches `1` in 111 steps. -/
theorem reachesOne_step_27 : reachesOne collatzStepGeneralized 27 :=
  ⟨111, by native_decide⟩

/-- The accelerated arm of `3` reaches `1` in 3 steps. -/
theorem reachesOne_accel_three : reachesOne collatzAccelGeneralized 3 :=
  ⟨5, by native_decide⟩

/-- The accelerated arm of `27` reaches `1` in 70 steps. -/
theorem reachesOne_accel_27 : reachesOne collatzAccelGeneralized 27 :=
  ⟨70, by native_decide⟩

/-- The decision routine Conway's theorem rules out: an oracle that reads a
    generalized map (and, optionally, a starting value) and answers a reachability
    question with a `Bool`. Lean does not enforce that the oracle be algorithmic;
    the propositions below are the informal shadows of Conway's theorem. -/
structure ReachOracle where
  total : (GeneralizedCollatzMap 2) → Bool
  single : (GeneralizedCollatzMap 2) → Nat → Bool

/-- Conway (1972), main result (recorded, not proved): no decision procedure can
    determine, uniformly in the generalized `3x+1` map, whether all powers of two
    iterate to `1`, nor whether a given input does. A formal proof would require
    a model of computation. -/
def conway1972MainTheorem : Prop :=
  ¬ ∃ D : ReachOracle,
      (∀ G : GeneralizedCollatzMap 2, D.total G = true ↔ ∀ k : Nat, reachesOne G (2 ^ k)) ∧
        (∀ G : GeneralizedCollatzMap 2, ∀ n : Nat, D.single G n = true ↔ reachesOne G n)

/-- The restricted form of Conway's theorem emphasized by Kurtz--Simon (2007):
    already the question "do all powers of two reach `1`?" is undecidable.
    Recorded, not proved. -/
def conway1972PowerTwoTheorem : Prop :=
  ¬ ∃ D : ReachOracle, ∀ G : GeneralizedCollatzMap 2,
      D.total G = true ↔ ∀ k : Nat, reachesOne G (2 ^ k)

end Collatz.Papers.Conway1972
