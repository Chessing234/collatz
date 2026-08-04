/-!
The accelerated 3x+1 map and derived notions.

The accelerated map folds together one odd step `3n+1` and the forced even
step `(3n+1)/2`, so every iterate strictly decreases when the input is even.
This module collects the map, its orbit, stopping-time predicates, parity
vectors, and a family of checked foundational lemmas that do not assume the
Collatz conjecture.
-/

namespace Collatz

/-- The accelerated 3x+1 map `T(n) = n/2` for even `n`, `(3n+1)/2` for odd `n`.
The value at `0` is `0` so that `T` is a total function on `Nat`. -/
def acceleratedStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Iteration of the accelerated map: `acceleratedOrbit k n = T^k(n)`. -/
def acceleratedOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => acceleratedOrbit k (acceleratedStep n)

section orbit_facts

/-- Zero iterations leave a state unchanged. -/
@[simp] theorem acceleratedOrbit_zero (n : Nat) : acceleratedOrbit 0 n = n := rfl

/-- One more iteration applies `acceleratedStep` first. -/
@[simp] theorem acceleratedOrbit_succ (k n : Nat) :
    acceleratedOrbit (k + 1) n = acceleratedOrbit k (acceleratedStep n) := rfl

/-- The accelerated map sends `0` to `0`. -/
@[simp] theorem acceleratedStep_zero : acceleratedStep 0 = 0 := by
  funext; simp [acceleratedStep]

/-- The accelerated map sends `1` to `2`. -/
@[simp] theorem acceleratedStep_one : acceleratedStep 1 = 2 := by
  funext; simp [acceleratedStep]

/-- The accelerated map sends `2` to `1`. -/
@[simp] theorem acceleratedStep_two : acceleratedStep 2 = 1 := by
  funext; simp [acceleratedStep]

/-- The accelerated map sends `3` to `5`. -/
@[simp] theorem acceleratedStep_three : acceleratedStep 3 = 5 := by
  funext; simp [acceleratedStep]

/-- The accelerated map sends `4` to `2`. -/
@[simp] theorem acceleratedStep_four : acceleratedStep 4 = 2 := by
  funext; simp [acceleratedStep]

/-- The accelerated map sends `5` to `8`. -/
@[simp] theorem acceleratedStep_five : acceleratedStep 5 = 8 := by
  funext; simp [acceleratedStep]

/-- The input `1` reaches `1`. -/
theorem one_reaches_one_accelerated : ∃ k : Nat, acceleratedOrbit k 1 = 1 := by
  exact ⟨2, by decide⟩

/-- The input `2` reaches `1`. -/
theorem two_reaches_one_accelerated : ∃ k : Nat, acceleratedOrbit k 2 = 1 := by
  exact ⟨1, by decide⟩

/-- The input `3` reaches `1`. -/
theorem three_reaches_one_accelerated : ∃ k : Nat, acceleratedOrbit k 3 = 1 := by
  exact ⟨5, by decide⟩

/-- The input `4` reaches `1`. -/
theorem four_reaches_one_accelerated : ∃ k : Nat, acceleratedOrbit k 4 = 1 := by
  exact ⟨2, by decide⟩

/-- `T^(k+1)(n) = T(T^k(n))`.  This orientation is convenient for inductive
proofs that inspect the last iterate. -/
theorem acceleratedOrbit_succ_step (k n : Nat) :
    acceleratedOrbit (k + 1) n = acceleratedStep (acceleratedOrbit k n) := by
  induction k generalizing n with
  | zero =>
    simp [acceleratedOrbit]
  | succ k ih =>
    calc
      acceleratedOrbit (k + 2) n
          = acceleratedOrbit (k + 1) (acceleratedStep n) := by simp [acceleratedOrbit_succ]
      _ = acceleratedStep (acceleratedOrbit k (acceleratedStep n)) := by rw [ih (acceleratedStep n)]
      _ = acceleratedStep (acceleratedOrbit (k + 1) n) := by simp [acceleratedOrbit_succ]

/-- The accelerated orbit of a positive input stays positive. -/
theorem acceleratedOrbit_positive {n : Nat} (hn : n > 0) (k : Nat) :
    acceleratedOrbit k n > 0 := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    have h : acceleratedOrbit (k + 1) n = acceleratedStep (acceleratedOrbit k n) := by
      apply acceleratedOrbit_succ_step
    rw [h]
    by_cases heven : (acceleratedOrbit k n) % 2 = 0
    · simp [acceleratedStep, heven]
      omega
    · have hodd : (acceleratedOrbit k n) % 2 = 1 := by omega
      simp [acceleratedStep, hodd]
      omega

/-- Iteration satisfies the semigroup law `T^(j+k)(n) = T^j(T^k(n))`. -/
theorem acceleratedOrbit_add (j k n : Nat) :
    acceleratedOrbit j (acceleratedOrbit k n) = acceleratedOrbit (j + k) n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h1 : acceleratedOrbit (j + (k + 1)) n = acceleratedOrbit (j + k) (acceleratedStep n) := by
      rw [show j + (k + 1) = (j + k) + 1 by omega]
      simp [acceleratedOrbit_succ]
    rw [h1]
    exact ih (acceleratedStep n)

end orbit_facts

section stopping_time

/-- `n` has a finite stopping time when some positive iterate of `T` drops
strictly below the starting value `n`. This is the predicate used in
Terras (1976). -/
def hasFiniteStoppingTime (n : Nat) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ acceleratedOrbit k n < n

/-- The stopping-time predicate: `stoppingTime n k` holds when `k ≥ 1` is the
least index with `T^k(n) < n`. -/
def stoppingTime (n : Nat) (k : Nat) : Prop :=
  1 ≤ k ∧ acceleratedOrbit k n < n ∧ ∀ j : Nat, 1 ≤ j → j < k → ¬(acceleratedOrbit j n < n)

/-- The total-stopping-time predicate: `totalStoppingTime n k` holds when `k`
is the least index with `T^k(n) = 1`. -/
def totalStoppingTime (n : Nat) (k : Nat) : Prop :=
  acceleratedOrbit k n = 1 ∧ ∀ j : Nat, j < k → acceleratedOrbit j n ≠ 1

/-- Every even positive `n` drops below itself after one accelerated step,
hence has stopping time `1`. -/
theorem hasFiniteStoppingTime_of_even {n : Nat} (hn : 0 < n) (heven : n % 2 = 0) :
    hasFiniteStoppingTime n := by
  refine ⟨1, ⟨by omega, ?_⟩⟩
  simp [acceleratedStep, heven]
  exact Nat.div_lt_self hn (by omega)

/-- If `n > 1` and its orbit reaches `1`, then the orbit must eventually drop
below `n`; therefore a finite total stopping time implies a finite stopping
time. -/
theorem hasFiniteStoppingTime_of_reaches_one {n : Nat} (hn : 1 < n)
    (h : ∃ k : Nat, acceleratedOrbit k n = 1) :
    hasFiniteStoppingTime n := by
  cases h with | intro k hk =>
  by_cases h' : ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ acceleratedOrbit j n < n
  · cases h' with | intro j h' =>
    cases h' with | intro hj1 h' =>
    cases h' with | intro hjk hj =>
    exact ⟨j, ⟨hj1, hj⟩⟩
  · have h'' : ∀ j : Nat, 1 ≤ j → j ≤ k → ¬(acceleratedOrbit j n < n) := by
      intro j hj1 hjk hdrop
      exact h' ⟨j, ⟨hj1, ⟨hjk, hdrop⟩⟩⟩
    have below : ∀ j : Nat, j ≤ k → acceleratedOrbit j n ≥ n := by
      intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := h'' (j + 1) (by omega) hj
        omega
    have final := below k (by omega)
    rw [hk] at final
    omega

/-- The stopping time of `2` is `1`. -/
theorem stoppingTime_two : stoppingTime 2 1 := by
  constructor
  · omega
  constructor
  · decide
  · intro j hj1 hj
    omega

/-- The stopping time of `3` is `4`. -/
theorem stoppingTime_three : stoppingTime 3 4 := by
  constructor
  · omega
  constructor
  · decide
  · intro j hj1 hj
    have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    cases this with
    | inl h => rw [h]; decide
    | inr h =>
      cases h with
      | inl h => rw [h]; decide
      | inr h => rw [h]; decide

/-- The stopping time of `4` is `1`. -/
theorem stoppingTime_four : stoppingTime 4 1 := by
  constructor
  · omega
  constructor
  · decide
  · intro j hj1 hj
    omega

/-- The stopping time of `5` is `2`. -/
theorem stoppingTime_five : stoppingTime 5 2 := by
  constructor
  · omega
  constructor
  · decide
  · intro j hj1 hj
    have : j = 1 := by omega
    rw [this]
    decide

/-- The stopping time of `7` is `7`. -/
theorem stoppingTime_seven : stoppingTime 7 7 := by
  constructor
  · omega
  constructor
  · decide
  · intro j hj1 hj
    have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    cases this with
    | inl h => rw [h]; decide
    | inr h =>
      cases h with
      | inl h => rw [h]; decide
      | inr h =>
        cases h with
        | inl h => rw [h]; decide
        | inr h =>
          cases h with
          | inl h => rw [h]; decide
          | inr h =>
            cases h with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide

/-- Bounded stopping-time predicate as a `Bool`: `n` has a stopping time `≤ B`.
Defined recursively so that it is computable and decidable. -/
def hasStoppingTimeBy (n B : Nat) : Bool :=
  match B with
  | 0 => false
  | B + 1 => hasStoppingTimeBy n B || (acceleratedOrbit (B + 1) n < n)

/-- The unbounded stopping-time predicate is equivalent to having a bounded
stopping time for some bound. -/
theorem hasFiniteStoppingTime_iff (n : Nat) :
    hasFiniteStoppingTime n ↔ ∃ B : Nat, hasStoppingTimeBy n B = true := by
  constructor
  · intro h
    cases h with | intro k h =>
    cases h with | intro _ hk =>
    exact ⟨k, by
      cases k with
      | zero => simp at hk
      | succ k =>
        have hk' : acceleratedOrbit k (acceleratedStep n) < n := by
          have eq : acceleratedOrbit k (acceleratedStep n) = acceleratedOrbit (k + 1) n := by
            have eq1 : acceleratedStep n = acceleratedOrbit 1 n := by
              simp [acceleratedOrbit]
            rw [eq1]
            rw [acceleratedOrbit_add k 1 n]
          rw [eq]
          exact hk
        simp [hasStoppingTimeBy, hk']⟩
  · intro h
    cases h with | intro B hB =>
    induction B with
    | zero => simp [hasStoppingTimeBy] at hB
    | succ B ih =>
      simp [hasStoppingTimeBy] at hB
      by_cases h' : hasStoppingTimeBy n B = true
      · exact ih h'
      · have : acceleratedOrbit (B + 1) n < n := by
          simp [h'] at hB
          exact of_decide_eq_true hB
        exact ⟨B + 1, ⟨by omega, this⟩⟩

/-- Number of indices `i ∈ [1, N]` satisfying `p`, given decidability of `p`. -/
def countUpTo (p : Nat → Prop) [∀ a, Decidable (p a)] (N : Nat) : Nat :=
  match N with
  | 0 => 0
  | n + 1 => countUpTo p n + if p (n + 1) then 1 else 0

end stopping_time

section parity_vectors

/-- The parity vector of length `j` for `n` records `(T^i(n) mod 2)` for
`i = 0, ..., j-1`. -/
def parityVector (n : Nat) (j : Nat) : List Nat :=
  List.range j |>.map (fun i => (acceleratedOrbit i n) % 2)

/-- The number of `1`s in the parity vector of length `j`, i.e. the number of
odd terms among the first `j` iterates. -/
def oddCount (n : Nat) (j : Nat) : Nat :=
  (parityVector n j).count 1

/-- Affine representation of `T^j(n)`: if `a` is the number of odd terms among
`n, T(n), ..., T^(j-1)(n)` and `b` is determined by the parity vector, then
`2^j · T^j(n) = 3^a · n + b`.  This is the standard inductive identity used in
Terras (1976) and many later papers. -/
theorem acceleratedOrbit_affine (n j : Nat) :
    ∃ b : Nat, 2^j * acceleratedOrbit j n = 3^(oddCount n j) * n + b := by
  induction j with
  | zero =>
    exact ⟨0, by simp [oddCount, parityVector]⟩
  | succ j ih =>
    cases ih with | intro b ih =>
    let a := oddCount n j
    have hstep : acceleratedOrbit (j + 1) n = acceleratedStep (acceleratedOrbit j n) := by
      apply acceleratedOrbit_succ_step
    by_cases hodd : (acceleratedOrbit j n) % 2 = 1
    · -- Odd step: T(x) = (3x+1)/2
      have hT : acceleratedStep (acceleratedOrbit j n) = (3 * acceleratedOrbit j n + 1) / 2 := by
        simp [acceleratedStep, hodd]
      rw [hstep, hT]
      have odd_a : oddCount n (j + 1) = a + 1 := by
        simp [a, oddCount, parityVector, hodd, List.range_succ]
      rw [odd_a]
      have dvd_odd : 2 ∣ (3 * acceleratedOrbit j n + 1) := by
        have : (3 * acceleratedOrbit j n + 1) % 2 = 0 := by
          omega
        exact Nat.dvd_of_mod_eq_zero this
      exact ⟨3 * b + 2^j, by
        rw [Nat.pow_succ, Nat.mul_assoc]
        rw [Nat.mul_div_cancel' dvd_odd]
        have step2 : 2^j * (3 * acceleratedOrbit j n + 1)
            = 3 * (2^j * acceleratedOrbit j n) + 2^j := by
          rw [Nat.mul_add]
          have : 2^j * (3 * acceleratedOrbit j n) = 3 * (2^j * acceleratedOrbit j n) := by
            rw [← Nat.mul_assoc]
            rw [show 2^j * 3 = 3 * 2^j by rw [Nat.mul_comm]]
            rw [Nat.mul_assoc]
          rw [this]
          simp
        rw [step2, ih]
        have step3 : 3 * (3^a * n + b) = 3^(a + 1) * n + 3 * b := by
          rw [Nat.mul_add]
          have : 3 * (3^a * n) = 3^(a + 1) * n := by
            rw [← Nat.mul_assoc]
            rw [show 3 * 3^a = 3^(a + 1) by rw [Nat.mul_comm]; rw [Nat.pow_add]]
          rw [this]
        rw [step3]
        omega⟩
    · -- Even step: T(x) = x/2
      have heven : (acceleratedOrbit j n) % 2 = 0 := by omega
      have hT : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n / 2 := by
        simp [acceleratedStep, heven]
      rw [hstep, hT]
      have even_a : oddCount n (j + 1) = a := by
        simp [a, oddCount, parityVector, heven, List.range_succ]
      rw [even_a]
      have dvd_even : 2 ∣ acceleratedOrbit j n := by
        exact Nat.dvd_of_mod_eq_zero heven
      exact ⟨b, by
        rw [Nat.pow_succ, Nat.mul_assoc]
        rw [Nat.mul_div_cancel' dvd_even, ih]⟩

end parity_vectors

end Collatz
