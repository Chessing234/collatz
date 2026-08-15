import Collatz.Basic
import Collatz.Accelerated
import Collatz.Core.Arith

/-!
# The reachability relation

The Collatz conjecture is a statement about a *relation*: `n` reaches `1`.
Working with the relation rather than with explicit iteration counts removes
most of the index bookkeeping from later arguments, so this file develops the
relation and its closure properties once and for all.

Two relations are developed in parallel, one for the standard map `C` and one
for the accelerated map `T`, together with the transfer lemmas between them.

The key structural facts proved here are:

* `Reaches` is reflexive and transitive (`reaches_refl`, `reaches_trans`);
* reaching `1` is invariant under one step in both directions
  (`reachesOne_iff_step`);
* reaching `1` is invariant under multiplication by powers of two
  (`reachesOne_two_mul_iff`, `reachesOne_two_pow_mul_iff`);
* the odd case reduces to `3n+1` (`reachesOne_odd_iff`).

Together these turn the conjecture into a statement about odd numbers only,
which is what every later file assumes.
-/

namespace Collatz
namespace Reach

/-! ## The standard reachability relation -/

/-- `Reaches n m` holds when some number of standard Collatz steps carries
`n` to `m`. -/
def Reaches (n m : Nat) : Prop := ∃ k : Nat, orbit k n = m

/-- `ReachesOne n` is the assertion that the standard orbit of `n` meets `1`. -/
def ReachesOne (n : Nat) : Prop := Reaches n 1

/-- Reachability is reflexive: zero steps suffice. -/
theorem reaches_refl (n : Nat) : Reaches n n := ⟨0, rfl⟩

/-- A single step is a reachability witness. -/
theorem reaches_step (n : Nat) : Reaches n (step n) := ⟨1, rfl⟩

/-- Any iterate is reachable. -/
theorem reaches_orbit (k n : Nat) : Reaches n (orbit k n) := ⟨k, rfl⟩

/-- Equal points are reachable from one another. -/
theorem reaches_of_eq {n m : Nat} (h : n = m) : Reaches n m := ⟨0, h⟩

/-- Reachability is transitive. -/
theorem reaches_trans {a b c : Nat} (h₁ : Reaches a b) (h₂ : Reaches b c) :
    Reaches a c := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  refine ⟨k + j, ?_⟩
  rw [orbit_add, hj, hk]

/-- Prefixing a step preserves reachability. -/
theorem reaches_of_step_reaches {n m : Nat} (h : Reaches (step n) m) :
    Reaches n m :=
  reaches_trans (reaches_step n) h

/-- Prefixing any number of steps preserves reachability. -/
theorem reaches_of_orbit_reaches {k n m : Nat} (h : Reaches (orbit k n) m) :
    Reaches n m :=
  reaches_trans (reaches_orbit k n) h

/-- Reaching a point that reaches `1` is enough to reach `1`. -/
theorem reachesOne_of_reaches {n m : Nat} (h : Reaches n m) (hm : ReachesOne m) :
    ReachesOne n :=
  reaches_trans h hm

/-! ## Stepping back and forth from `1` -/

/-- `1` reaches `1`. -/
theorem reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩

/-- If a step of `n` reaches `1`, so does `n`. -/
theorem reachesOne_of_step {n : Nat} (h : ReachesOne (step n)) : ReachesOne n :=
  reaches_of_step_reaches h

/-- If `n` reaches `1` in at least one step, its step reaches `1`.
The hypothesis `n ≠ 1` is not needed because `1` itself returns to `1`. -/
theorem reachesOne_step_of_reachesOne {n : Nat} (h : ReachesOne n) :
    ReachesOne (step n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    have hn : n = 1 := hk
    subst hn
    exact ⟨2, by decide⟩
  | succ k => exact ⟨k, hk⟩

/-- Reaching `1` is invariant under one Collatz step, in both directions. -/
theorem reachesOne_iff_step (n : Nat) : ReachesOne n ↔ ReachesOne (step n) :=
  ⟨reachesOne_step_of_reachesOne, reachesOne_of_step⟩

/-- Reaching `1` is invariant under any number of Collatz steps. -/
theorem reachesOne_iff_orbit (k n : Nat) : ReachesOne n ↔ ReachesOne (orbit k n) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih =>
    rw [orbit_succ_steps, ← ih (step n), ← reachesOne_iff_step]

/-! ## Powers of two -/

/-- A positive even number reaches `1` exactly when its half does. -/
theorem reachesOne_two_mul_iff (n : Nat) : ReachesOne (2 * n) ↔ ReachesOne n := by
  cases n with
  | zero =>
    constructor
    · intro h; exact h
    · intro h; exact h
  | succ m =>
    have hstep : step (2 * (m + 1)) = m + 1 := by
      have h0 : 2 * (m + 1) ≠ 0 := by omega
      have he : (2 * (m + 1)) % 2 = 0 := by omega
      rw [step, if_neg h0, if_pos he]
      exact Nat.mul_div_cancel_left _ (by omega)
    constructor
    · intro h
      have := (reachesOne_iff_step (2 * (m + 1))).mp h
      rwa [hstep] at this
    · intro h
      refine reachesOne_of_step ?_
      rwa [hstep]

/-- Doubling preserves the property of reaching `1`. -/
theorem reachesOne_two_mul {n : Nat} (h : ReachesOne n) : ReachesOne (2 * n) :=
  (reachesOne_two_mul_iff n).mpr h

/-- Halving an even number preserves the property of reaching `1`. -/
theorem reachesOne_div_two {n : Nat} (heven : n % 2 = 0) (h : ReachesOne n) :
    ReachesOne (n / 2) := by
  have hn : 2 * (n / 2) = n := by omega
  exact (reachesOne_two_mul_iff (n / 2)).mp (by rw [hn]; exact h)

/-- Multiplying by a power of two preserves reaching `1`, in both directions. -/
theorem reachesOne_two_pow_mul_iff (k n : Nat) :
    ReachesOne (2 ^ k * n) ↔ ReachesOne n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Arith.two_pow_succ, Nat.mul_assoc, reachesOne_two_mul_iff, ih]

/-- Every power of two reaches `1`. -/
theorem reachesOne_two_pow (k : Nat) : ReachesOne (2 ^ k) := by
  have := (reachesOne_two_pow_mul_iff k 1).mpr reachesOne_one
  simpa using this

/-! ## The odd case -/

/-- On an odd input the step map is `3n+1`. -/
theorem step_odd {n : Nat} (_hn : 0 < n) (hodd : n % 2 = 1) : step n = 3 * n + 1 := by
  have h0 : n ≠ 0 := by omega
  rw [step, if_neg h0, if_neg (show n % 2 ≠ 0 by omega)]

/-- On a positive even input the step map is halving. -/
theorem step_even {n : Nat} (_hn : 0 < n) (heven : n % 2 = 0) : step n = n / 2 := by
  have h0 : n ≠ 0 := by omega
  rw [step, if_neg h0, if_pos heven]

/-- An odd number reaches `1` exactly when `3n+1` does. -/
theorem reachesOne_odd_iff {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    ReachesOne n ↔ ReachesOne (3 * n + 1) := by
  rw [reachesOne_iff_step n, step_odd hn hodd]

/-- An odd number reaches `1` exactly when the accelerated value `(3n+1)/2` does. -/
theorem reachesOne_odd_iff_half {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    ReachesOne n ↔ ReachesOne ((3 * n + 1) / 2) := by
  have h : 2 * ((3 * n + 1) / 2) = 3 * n + 1 := by omega
  have h2 : ReachesOne (2 * ((3 * n + 1) / 2)) ↔ ReachesOne ((3 * n + 1) / 2) :=
    reachesOne_two_mul_iff _
  rw [h] at h2
  rw [reachesOne_odd_iff hn hodd]
  exact h2

/-- Reaching `1` for a positive even number reduces to its half. -/
theorem reachesOne_even_iff {n : Nat} (hn : 0 < n) (heven : n % 2 = 0) :
    ReachesOne n ↔ ReachesOne (n / 2) := by
  rw [reachesOne_iff_step n, step_even hn heven]

/-! ## Small concrete values

These are the base cases of every descent argument in the project. -/

theorem reachesOne_two : ReachesOne 2 := ⟨1, by decide⟩
theorem reachesOne_three : ReachesOne 3 := ⟨7, by decide⟩
theorem reachesOne_four : ReachesOne 4 := ⟨2, by decide⟩
theorem reachesOne_five : ReachesOne 5 := ⟨5, by decide⟩
theorem reachesOne_six : ReachesOne 6 := ⟨8, by decide⟩
theorem reachesOne_seven : ReachesOne 7 := ⟨16, by decide⟩
theorem reachesOne_eight : ReachesOne 8 := ⟨3, by decide⟩
theorem reachesOne_nine : ReachesOne 9 := ⟨19, by decide⟩
theorem reachesOne_ten : ReachesOne 10 := ⟨6, by decide⟩
theorem reachesOne_eleven : ReachesOne 11 := ⟨14, by decide⟩
theorem reachesOne_twelve : ReachesOne 12 := ⟨9, by decide⟩
theorem reachesOne_thirteen : ReachesOne 13 := ⟨9, by decide⟩
theorem reachesOne_fourteen : ReachesOne 14 := ⟨17, by decide⟩
theorem reachesOne_fifteen : ReachesOne 15 := ⟨17, by decide⟩
theorem reachesOne_sixteen : ReachesOne 16 := ⟨4, by decide⟩
theorem reachesOne_seventeen : ReachesOne 17 := ⟨12, by decide⟩
theorem reachesOne_eighteen : ReachesOne 18 := ⟨20, by decide⟩
theorem reachesOne_nineteen : ReachesOne 19 := ⟨20, by decide⟩
theorem reachesOne_twenty : ReachesOne 20 := ⟨7, by decide⟩
theorem reachesOne_twentyone : ReachesOne 21 := ⟨7, by decide⟩
theorem reachesOne_twentytwo : ReachesOne 22 := ⟨15, by decide⟩
theorem reachesOne_twentythree : ReachesOne 23 := ⟨15, by decide⟩
set_option maxRecDepth 20000 in
theorem reachesOne_twentyseven : ReachesOne 27 := ⟨111, by decide⟩

/-! ## The accelerated reachability relation -/

/-- `AccReaches n m` holds when some number of accelerated steps carries `n`
to `m`. -/
def AccReaches (n m : Nat) : Prop := ∃ k : Nat, acceleratedOrbit k n = m

/-- `AccReachesOne n` is the assertion that the accelerated orbit meets `1`. -/
def AccReachesOne (n : Nat) : Prop := AccReaches n 1

/-- Accelerated reachability is reflexive. -/
theorem accReaches_refl (n : Nat) : AccReaches n n := ⟨0, rfl⟩

/-- One accelerated step is a reachability witness. -/
theorem accReaches_step (n : Nat) : AccReaches n (acceleratedStep n) := ⟨1, rfl⟩

/-- Any accelerated iterate is reachable. -/
theorem accReaches_orbit (k n : Nat) : AccReaches n (acceleratedOrbit k n) := ⟨k, rfl⟩

/-- Accelerated reachability is transitive. -/
theorem accReaches_trans {a b c : Nat} (h₁ : AccReaches a b) (h₂ : AccReaches b c) :
    AccReaches a c := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  refine ⟨k + j, ?_⟩
  rw [← acceleratedOrbit_add, hj, hk]

/-- Prefixing an accelerated step preserves reachability. -/
theorem accReaches_of_step_reaches {n m : Nat} (h : AccReaches (acceleratedStep n) m) :
    AccReaches n m :=
  accReaches_trans (accReaches_step n) h

/-- `1` is accelerated-reachable from `1`. -/
theorem accReachesOne_one : AccReachesOne 1 := ⟨0, rfl⟩

/-- If the accelerated step of `n` reaches `1`, so does `n`. -/
theorem accReachesOne_of_step {n : Nat} (h : AccReachesOne (acceleratedStep n)) :
    AccReachesOne n :=
  accReaches_of_step_reaches h

/-! ## Transfer between the two maps -/

/-- One accelerated step is one standard step on positive even inputs. -/
theorem accStep_eq_step_of_even {n : Nat} (heven : n % 2 = 0) :
    acceleratedStep n = step n := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [acceleratedStep, if_pos heven, step_even (Nat.succ_pos m) heven]

/-- One accelerated step is two standard steps on odd inputs. -/
theorem accStep_eq_step_step_of_odd {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    acceleratedStep n = step (step n) := by
  have h1 : acceleratedStep n = (3 * n + 1) / 2 := by
    rw [acceleratedStep, if_neg (show n % 2 ≠ 0 by omega)]
  have h2 : step n = 3 * n + 1 := step_odd hn hodd
  have h3 : (3 * n + 1) % 2 = 0 := by omega
  have h4 : 0 < 3 * n + 1 := by omega
  rw [h1, h2, step_even h4 h3]

/-- The accelerated step of a positive number reaches `1` under the standard map
exactly when the number itself does. -/
theorem reachesOne_accStep_iff {n : Nat} (hn : 0 < n) :
    ReachesOne n ↔ ReachesOne (acceleratedStep n) := by
  rcases Arith.mod_two_eq_zero_or_one n with heven | hodd
  · rw [accStep_eq_step_of_even heven, reachesOne_iff_step]
  · rw [accStep_eq_step_step_of_odd hn hodd, ← reachesOne_iff_step, ← reachesOne_iff_step]

/-- Reaching `1` is invariant under any number of accelerated steps.  This is
the workhorse for descent arguments: showing that some accelerated iterate of
`n` reaches `1` is the same as showing that `n` does. -/
theorem reachesOne_accOrbit_iff {n : Nat} (hn : 0 < n) (k : Nat) :
    ReachesOne n ↔ ReachesOne (acceleratedOrbit k n) := by
  induction k generalizing n with
  | zero => rw [acceleratedOrbit]
  | succ k ih =>
    have hpos : 0 < acceleratedStep n := by
      have h1 := acceleratedOrbit_positive hn 1
      rw [acceleratedOrbit, acceleratedOrbit] at h1
      exact h1
    rw [acceleratedOrbit, ← ih hpos, ← reachesOne_accStep_iff hn]

/-- If some accelerated iterate reaches `1`, so does the starting point. -/
theorem reachesOne_of_accOrbit {n k : Nat} (hn : 0 < n)
    (h : ReachesOne (acceleratedOrbit k n)) : ReachesOne n :=
  (reachesOne_accOrbit_iff hn k).mpr h

/-- Accelerated reachability of `1` implies standard reachability of `1`. -/
theorem reachesOne_of_accReachesOne {n : Nat} (hn : 0 < n) (h : AccReachesOne n) :
    ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing n with
  | zero =>
    rw [acceleratedOrbit] at hk
    subst hk
    exact reachesOne_one
  | succ k ih =>
    rw [acceleratedOrbit] at hk
    have hpos : 0 < acceleratedStep n := by
      have := acceleratedOrbit_positive hn 1
      rw [acceleratedOrbit, acceleratedOrbit] at this
      exact this
    exact (reachesOne_accStep_iff hn).mpr (ih hpos hk)

end Reach
end Collatz
