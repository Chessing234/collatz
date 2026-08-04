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

/-- The bounded stopping-time predicate is monotone in the bound: if `n` has a
stopping time `≤ B` and `B ≤ B'`, then `n` has a stopping time `≤ B'`. -/
theorem hasStoppingTimeBy_monotone {n B B' : Nat} (hB : hasStoppingTimeBy n B = true) (hle : B ≤ B') :
    hasStoppingTimeBy n B' = true := by
  have h : ∀ B' : Nat, B ≤ B' → hasStoppingTimeBy n B' = true := by
    intro B' hle
    induction B' with
    | zero =>
      have : B = 0 := by omega
      simp [this, hasStoppingTimeBy] at hB
    | succ B'' ih =>
      by_cases h : B ≤ B''
      · have h' := ih h
        simp [hasStoppingTimeBy, h']
      · have : B = B'' + 1 := by omega
        rw [this] at hB
        exact hB
  exact h B' hle

/-- Doubling a number with finite stopping time gives a number with finite
stopping time: the orbit of `2m` halves on the first accelerated step. -/
theorem hasFiniteStoppingTime_of_double {m : Nat} (hm : hasFiniteStoppingTime m) :
    hasFiniteStoppingTime (2 * m) := by
  cases hm with
  | intro k h =>
    cases h with
    | intro hk1 hk =>
      have hstep : acceleratedStep (2 * m) = m := by
        simp [acceleratedStep]
      refine ⟨k + 1, ⟨by omega, ?_⟩⟩
      have h1 : acceleratedOrbit (k + 1) (2 * m) = acceleratedOrbit k m := by
        calc
          acceleratedOrbit (k + 1) (2 * m)
            = acceleratedOrbit k (acceleratedStep (2 * m)) := by simp [acceleratedOrbit_succ]
          _ = acceleratedOrbit k m := by rw [hstep]
      rw [h1]
      omega

/-- Multiplying a number with finite stopping time by a positive power of two
preserves finite stopping time, iterating the halving behaviour of the
accelerated step. -/
theorem hasFiniteStoppingTime_of_multiple {m a : Nat} (hm : hasFiniteStoppingTime m) (ha : 0 < a) :
    hasFiniteStoppingTime (2^a * m) := by
  induction a with
  | zero =>
    omega
  | succ a ih =>
    by_cases ha0 : a = 0
    · simp [ha0]
      exact hasFiniteStoppingTime_of_double hm
    · have h1 : 0 < a := by omega
      have h2 : 2^(a + 1) * m = 2 * (2^a * m) := by
        rw [Nat.pow_succ]
        rw [show 2^a * 2 = 2 * 2^a by rw [Nat.mul_comm]]
        rw [← Nat.mul_assoc]
      rw [h2]
      have h3 : hasFiniteStoppingTime (2^a * m) := ih h1
      exact hasFiniteStoppingTime_of_double h3

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

-- Private lemmas supporting the completeness theorems for parity vectors.

private theorem two_pow_pos (k : Nat) : 0 < 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

private theorem two_mul_mod_two_mul (x m : Nat) : (2 * x) % (2 * m) = 2 * (x % m) := by
  by_cases hm : m = 0
  · simp [hm]
  · have h1 : 2 * x = 2 * m * (x / m) + 2 * (x % m) := by
      have : 2 * x = 2 * (m * (x / m) + x % m) := by
        rw [Nat.div_add_mod]
      rw [this]
      rw [Nat.mul_add]
      rw [← Nat.mul_assoc]
    rw [h1]
    have h2 : 2 * m * (x / m) + 2 * (x % m) = 2 * (x % m) + (2 * m) * (x / m) := by
      rw [Nat.add_comm]
    rw [h2]
    rw [Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have h3 : x % m < m := by
      apply Nat.mod_lt
      omega
    omega

private theorem mod_eq_of_dvd' {n a b : Nat} (h1 : n ∣ a - b) (h2 : a ≥ b) : a % n = b % n := by
  cases h1 with | intro c hc =>
  have h3 : a = b + n * c := by omega
  rw [h3]
  rw [Nat.add_mul_mod_self_left]

private theorem add_mod_cancel_right (a b c n : Nat) (h : (a + c) % n = (b + c) % n) : a % n = b % n := by
  by_cases hab : a ≥ b
  · have h2 : (a + c) % n = (b + c) % n := h
    have h3 : n ∣ (a + c) - (b + c) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)
    have h4 : (a + c) - (b + c) = a - b := by
      omega
    rw [h4] at h3
    exact mod_eq_of_dvd' h3 hab
  · have h2 : (b + c) % n = (a + c) % n := by rw [h]
    have h3 : n ∣ (b + c) - (a + c) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)
    have h4 : (b + c) - (a + c) = b - a := by
      omega
    rw [h4] at h3
    have h5 : b % n = a % n := mod_eq_of_dvd' h3 (by omega)
    exact h5.symm

private theorem mul_mod_distrib_left (a b n : Nat) : (a * (b % n)) % n = (a * b) % n := by
  rw [Nat.mul_mod]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod]

private theorem mul_mod_distrib_right (a b n : Nat) : ((a % n) * b) % n = (a * b) % n := by
  rw [Nat.mul_mod]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod]

private theorem mul_mod_of_inv (u x n : Nat) (h : (3 * u) % n = 1 % n) :
    3 * ((u * x) % n) % n = x % n := by
  have h1 : 3 * ((u * x) % n) % n = (3 * (u * x)) % n := by
    rw [mul_mod_distrib_left]
  have h2 : (3 * (u * x)) % n = (3 * u * x) % n := by
    rw [Nat.mul_assoc]
  have h3 : (3 * u * x) % n = ((3 * u) % n * x) % n := by
    rw [← mul_mod_distrib_right]
  rw [h1, h2, h3, h]
  have h4 : (1 % n * x) % n = x % n := by
    by_cases hn : n = 0
    · simp [hn]
    · by_cases hn1 : n = 1
      · simp [hn1, Nat.mod_one]
      · have h1n : 1 % n = 1 := by apply Nat.mod_eq_of_lt; omega
        simp [h1n]
  exact h4

/-- The parity vector of length `k+1` decomposes into the first parity bit and the parity vector of the accelerated step. -/
private theorem parityVector_succ (n k : Nat) :
    parityVector n (k + 1) = (n % 2) :: parityVector (acceleratedStep n) k := by
  induction k with
  | zero =>
    simp [parityVector]
  | succ k ih =>
    have h1 : parityVector n (k + 2) = parityVector n (k + 1) ++ [acceleratedOrbit (k + 1) n % 2] := by
      simp [parityVector, List.range_succ]
    have h2 : parityVector (acceleratedStep n) (k + 1) = parityVector (acceleratedStep n) k ++ [acceleratedOrbit k (acceleratedStep n) % 2] := by
      simp [parityVector, List.range_succ]
    rw [h1, h2, ih]
    have h3 : acceleratedOrbit (k + 1) n % 2 = acceleratedOrbit k (acceleratedStep n) % 2 := by
      rw [acceleratedOrbit_succ]
    rw [h3]
    simp

/-- If two even numbers are congruent modulo 2^(k+1), their halves are congruent modulo 2^k. -/
private theorem div_two_mod_of_mod_pow_succ {a b k : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0)
    (h : a % 2^(k+1) = b % 2^(k+1)) : (a / 2) % 2^k = (b / 2) % 2^k := by
  have h1 : a = 2 * (a / 2) := by
    rw [← Nat.div_add_mod a 2, ha]
    omega
  have h2 : b = 2 * (b / 2) := by
    rw [← Nat.div_add_mod b 2, hb]
    omega
  have h3 : 2 * (a / 2) % (2 * (2^k)) = 2 * (b / 2) % (2 * (2^k)) := by
    rw [← h1, ← h2]
    rw [show 2 * (2^k) = 2^(k+1) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
    exact h
  rw [two_mul_mod_two_mul (a / 2) (2^k), two_mul_mod_two_mul (b / 2) (2^k)] at h3
  omega

/-- If halves of two even numbers are congruent modulo 2^k, the numbers are congruent modulo 2^(k+1). -/
private theorem mod_pow_succ_of_div_two_mod {a b k : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0)
    (h : (a / 2) % 2^k = (b / 2) % 2^k) : a % 2^(k+1) = b % 2^(k+1) := by
  have h1 : a = 2 * (a / 2) := by
    rw [← Nat.div_add_mod a 2, ha]
    omega
  have h2 : b = 2 * (b / 2) := by
    rw [← Nat.div_add_mod b 2, hb]
    omega
  have h3 : (a / 2) % 2^k = (b / 2) % 2^k := h
  rw [h1, h2]
  rw [show 2^(k+1) = 2 * (2^k) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
  rw [two_mul_mod_two_mul (a / 2) (2^k), two_mul_mod_two_mul (b / 2) (2^k)]
  rw [h3]

/-- The accelerated step commutes with reduction modulo 2^(k+1) as far as residues modulo 2^k are concerned. -/
private theorem acceleratedStep_mod_eq (n k : Nat) :
    acceleratedStep n % 2^k = acceleratedStep (n % 2^(k+1)) % 2^k := by
  by_cases heven : n % 2 = 0
  · -- even case
    have h1 : acceleratedStep n = n / 2 := by simp [acceleratedStep, heven]
    have h2 : (n % 2^(k+1)) % 2 = 0 := by
      have : n % 2^(k+1) % 2 = n % 2 := by
        rw [Nat.mod_mod_of_dvd n (by refine ⟨2^k, ?_⟩; rw [Nat.pow_succ]; rw [Nat.mul_comm])]
      rw [this, heven]
    have h3 : acceleratedStep (n % 2^(k+1)) = (n % 2^(k+1)) / 2 := by simp [acceleratedStep, h2]
    rw [h1, h3]
    have h4 : n % 2^(k+1) = 2 * ((n / 2) % 2^k) := by
      have hdiv2 : ∃ m, n = 2 * m := ⟨n / 2, by rw [← Nat.div_add_mod n 2, heven]; omega⟩
      cases hdiv2 with | intro m hm =>
      have hn2m : n / 2 = m := by
        rw [hm]
        omega
      rw [hn2m]
      rw [hm]
      rw [show 2^(k+1) = 2 * (2^k) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
      rw [two_mul_mod_two_mul]
    have h5 : (n % 2^(k+1)) / 2 = (n / 2) % 2^k := by
      rw [h4]
      omega
    rw [h5]
    rw [Nat.mod_mod]
  · -- odd case
    have hodd : n % 2 = 1 := by omega
    have h1 : acceleratedStep n = (3 * n + 1) / 2 := by simp [acceleratedStep, hodd]
    have h2 : (n % 2^(k+1)) % 2 = 1 := by
      have : n % 2^(k+1) % 2 = n % 2 := by
        rw [Nat.mod_mod_of_dvd n (by refine ⟨2^k, ?_⟩; rw [Nat.pow_succ]; rw [Nat.mul_comm])]
      rw [this, hodd]
    have h3 : acceleratedStep (n % 2^(k+1)) = (3 * (n % 2^(k+1)) + 1) / 2 := by simp [acceleratedStep, h2]
    rw [h1, h3]
    apply div_two_mod_of_mod_pow_succ
    · omega
    · omega
    · have h4 : (3 * (n % 2^(k+1)) + 1) % 2^(k+1) = (3 * n + 1) % 2^(k+1) := by
        have h5 : 3 * (n % 2^(k+1)) % 2^(k+1) = 3 * n % 2^(k+1) := by
          simp [Nat.mul_mod]
        have h6 : (3 * (n % 2^(k+1)) + 1) % 2^(k+1) = ((3 * (n % 2^(k+1))) % 2^(k+1) + 1 % 2^(k+1)) % 2^(k+1) := by
          rw [Nat.add_mod]
        have h7 : (3 * n + 1) % 2^(k+1) = ((3 * n) % 2^(k+1) + 1 % 2^(k+1)) % 2^(k+1) := by
          rw [Nat.add_mod]
        rw [h6, h7, h5]
      exact h4.symm

/-- If `2` divides `3*y`, then `2` divides `y`. -/
private theorem two_dvd_of_dvd_three (y : Nat) (h : 2 ∣ 3 * y) : 2 ∣ y := by
  have h1 : (3 * y) % 2 = 0 := by
    exact Nat.dvd_iff_mod_eq_zero.mp h
  have h2 : y % 2 = 0 := by
    have : (3 * y) % 2 = y % 2 := by
      simp [Nat.mul_mod]
    rw [this] at h1
    exact h1
  exact Nat.dvd_of_mod_eq_zero h2

/-- If `2^k` divides `3*x`, then `2^k` divides `x`. -/
private theorem two_pow_dvd_of_dvd_three_mul (k x : Nat) (h : 2^k ∣ 3 * x) : 2^k ∣ x := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h1 : 2^k ∣ 2^(k+1) := by
      refine ⟨2, ?_⟩
      rw [Nat.pow_succ]
    have h2 : 2^k ∣ 3 * x := by
      exact Nat.dvd_trans h1 h
    have h3 : 2^k ∣ x := ih h2
    cases h3 with | intro y hy =>
    rw [hy] at h
    have h4 : 3 * (2^k * y) = 2^k * (3 * y) := by
      calc
        3 * (2^k * y) = 3 * (2^k) * y := by rw [Nat.mul_assoc]
        _ = (2^k) * 3 * y := by rw [Nat.mul_comm 3 (2^k)]
        _ = (2^k) * (3 * y) := by rw [Nat.mul_assoc]
    have h5 : 2^k * 2 ∣ 3 * (2^k * y) := by
      rw [show 2^(k+1) = (2^k) * 2 by rw [Nat.pow_succ]] at h
      exact h
    rw [h4] at h5
    have h6 : 2 ∣ 3 * y := by
      apply Nat.dvd_of_mul_dvd_mul_left (two_pow_pos k) h5
    have h7 : 2 ∣ y := two_dvd_of_dvd_three y h6
    cases h7 with | intro z hz =>
    refine ⟨z, ?_⟩
    calc
      x = 2^k * y := by rw [hy]
      _ = 2^k * (2 * z) := by rw [hz]
      _ = 2^k * 2 * z := by
        rw [Nat.mul_assoc]
      _ = 2^(k+1) * z := by
        rw [Nat.pow_succ]

/-- Cancel a factor of 3 modulo a power of two. -/
private theorem mul_three_cancel_mod_pow_two (k a b : Nat)
    (h : (3 * a) % 2^k = (3 * b) % 2^k) : a % 2^k = b % 2^k := by
  by_cases hab : a ≥ b
  · have h2 : (3 * a) % 2^k = (3 * b) % 2^k := h
    have h3 : 2^k ∣ 3 * a - 3 * b := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)
    have h4 : 3 * a - 3 * b = 3 * (a - b) := by
      rw [Nat.mul_sub]
    rw [h4] at h3
    have h5 : 2^k ∣ (a - b) := two_pow_dvd_of_dvd_three_mul k (a - b) h3
    exact mod_eq_of_dvd' h5 hab
  · have h2 : (3 * b) % 2^k = (3 * a) % 2^k := by rw [h]
    have h3 : 2^k ∣ 3 * b - 3 * a := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)
    have h4 : 3 * b - 3 * a = 3 * (b - a) := by
      rw [Nat.mul_sub]
    rw [h4] at h3
    have h5 : 2^k ∣ (b - a) := two_pow_dvd_of_dvd_three_mul k (b - a) h3
    have h6 : b % 2^k = a % 2^k := mod_eq_of_dvd' h5 (by omega)
    exact h6.symm

/-- If `x < 2^(k+1)` and `x % 2^k = 1`, then `x = 1` or `x = 1 + 2^k`. -/
private theorem mod_pow_two_eq_one_or_one_add (x k : Nat) (hlt : x < 2^(k+1)) (hmod : x % 2^k = 1) :
    x = 1 ∨ x = 1 + 2^k := by
  let q := x / 2^k
  let r := x % 2^k
  have hdiv : x = 2^k * q + r := by
    rw [Nat.div_add_mod x (2^k)]
  have hr : r = 1 := by
    simp [r, hmod]
  rw [hr] at hdiv
  have h1 : x = 2^k * q + 1 := by
    exact hdiv
  have h2 : q < 2 := by
    apply Nat.div_lt_of_lt_mul
    exact hlt
  have h3 : q = 0 ∨ q = 1 := by
    cases hq : q with
    | zero => left; rfl
    | succ n =>
      cases n with
      | zero => right; rfl
      | succ n =>
        have h4 : q ≥ 2 := by
          rw [hq]
          apply Nat.succ_le_succ
          apply Nat.succ_le_succ
          apply Nat.zero_le
        rw [hq] at h4 h2
        omega
  cases h3 with
  | inl h0 =>
    left
    rw [h0] at h1
    omega
  | inr h1' =>
    right
    rw [h1'] at h1
    have : x = 1 + 2^k := by
      rw [h1]
      omega
    exact this

/-- Adding a multiple of `m` does not change the residue modulo `m`. -/
private theorem add_multiple_mod_eq (a m n : Nat) (h : m ∣ n) : (a + n) % m = a % m := by
  cases h with | intro c hc =>
  rw [hc]
  rw [Nat.add_mul_mod_self_left]

/-- The inverse of 3 modulo 2^k, constructed by Hensel lifting. -/
private def inv3Mod (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 =>
    let u := inv3Mod k
    if 3 * u % 2^(k+1) = 1 then u else u + 2^k

private theorem inv3Mod_rec (k : Nat) :
    inv3Mod (k + 1) = if 3 * (inv3Mod k) % 2^(k+1) = 1 then inv3Mod k else inv3Mod k + 2^k := by
  rfl

private theorem inv3Mod_spec (k : Nat) : 3 * (inv3Mod k) % 2^k = 1 % 2^k := by
  induction k with
  | zero =>
    simp [inv3Mod]
  | succ k ih =>
    cases k with
    | zero =>
      simp [inv3Mod]
    | succ k =>
      rw [inv3Mod_rec (k + 1)]
      by_cases h : 3 * (inv3Mod (k + 1)) % 2^(k + 2) = 1
      · simp [h]
      · simp [h]
        have h1 : 3 * (inv3Mod (k + 1)) % 2^(k + 1) = 1 % 2^(k + 1) := ih
        have h2 : 3 * (inv3Mod (k + 1)) % 2^(k + 2) ≠ 1 := by
          intro h'
          exact h h'
        have h1' : 1 % 2^(k + 1) = 1 := by
          apply Nat.mod_eq_of_lt
          apply Nat.one_lt_pow
          omega
          omega
        have h3 : 3 * (inv3Mod (k + 1)) % 2^(k + 2) = 1 + 2^(k + 1) := by
          have hmod : (3 * (inv3Mod (k + 1)) % 2^(k + 2)) % 2^(k + 1) = 1 := by
            rw [Nat.mod_mod_of_dvd (3 * (inv3Mod (k + 1))) (by refine ⟨2, ?_⟩; rw [Nat.pow_succ])]
            rw [h1'] at h1
            exact h1
          have hlt : 3 * (inv3Mod (k + 1)) % 2^(k + 2) < 2^(k + 2) := by
            apply Nat.mod_lt
            apply two_pow_pos
          have : 3 * (inv3Mod (k + 1)) % 2^(k + 2) = 1 ∨ 3 * (inv3Mod (k + 1)) % 2^(k + 2) = 1 + 2^(k + 1) := by
            apply mod_pow_two_eq_one_or_one_add
            exact hlt
            exact hmod
          cases this with
          | inl h1' =>
            exfalso
            exact h2 h1'
          | inr h2' =>
            exact h2'
        calc
          3 * (inv3Mod (k + 1) + 2^(k + 1)) % 2^(k + 2)
            = (3 * inv3Mod (k + 1) + 3 * 2^(k + 1)) % 2^(k + 2) := by simp [Nat.mul_add]
          _ = ((3 * inv3Mod (k + 1)) % 2^(k + 2) + (3 * 2^(k + 1)) % 2^(k + 2)) % 2^(k + 2) := by
            rw [Nat.add_mod]
          _ = ((1 + 2^(k + 1)) + 2^(k + 1)) % 2^(k + 2) := by
            rw [h3]
            congr
            have h3pow : (3 * 2^(k + 1)) % 2^(k + 2) = 2^(k + 1) := by
              rw [show 2^(k+2) = 2 * 2^(k+1) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
              have h3pow' : 3 * 2^(k+1) = 2 * 2^(k+1) + 2^(k+1) := by omega
              rw [h3pow']
              rw [Nat.add_mod]
              simp [Nat.mod_self]
              apply Nat.mod_eq_of_lt
              omega
            exact h3pow
          _ = 1 := by
            have h4 : (1 + 2^(k + 1)) + 2^(k + 1) = 1 + 2^(k + 2) := by
              have h5 : 2^(k + 1) + 2^(k + 1) = 2^(k + 2) := by
                calc
                  2^(k + 1) + 2^(k + 1)
                    = 2 * 2^(k + 1) := by rw [Nat.two_mul]
                  _ = 2^(k + 2) := by
                    rw [Nat.mul_comm]
                    rw [← Nat.pow_succ]
              calc
                (1 + 2^(k + 1)) + 2^(k + 1)
                  = 1 + (2^(k + 1) + 2^(k + 1)) := by rw [Nat.add_assoc]
                _ = 1 + 2^(k + 2) := by rw [h5]
            rw [h4]
            have h5 : (1 + 2^(k+2)) % 2^(k+2) = 1 := by
              have h6 : (1 + 2^(k+2)) % 2^(k+2) = 1 % 2^(k+2) := by
                have h7 : 1 + 2^(k+2) = 1 + 2^(k+2) * 1 := by simp
                rw [h7]
                rw [Nat.add_mul_mod_self_left]
              rw [h6]
              apply Nat.mod_eq_of_lt
              apply Nat.one_lt_pow
              omega
              omega
            exact h5

/-- The parity vector of length `k` is periodic with period `2^k`. -/
theorem parityVector_mod_pow_two (n k : Nat) : parityVector n k = parityVector (n % 2^k) k := by
  induction k generalizing n with
  | zero =>
    simp [parityVector]
  | succ k ih =>
    rw [parityVector_succ n k]
    rw [parityVector_succ (n % 2^(k+1)) k]
    have hhead : n % 2 = (n % 2^(k+1)) % 2 := by
      rw [Nat.mod_mod_of_dvd n (by refine ⟨2^k, ?_⟩; rw [Nat.pow_succ]; rw [Nat.mul_comm])]
    rw [hhead]
    have htails : parityVector (acceleratedStep n) k = parityVector (acceleratedStep (n % 2^(k+1))) k := by
      calc
        parityVector (acceleratedStep n) k
          = parityVector (acceleratedStep n % 2^k) k := by rw [ih (acceleratedStep n)]
        _ = parityVector (acceleratedStep (n % 2^(k+1)) % 2^k) k := by
          rw [acceleratedStep_mod_eq n k]
        _ = parityVector (acceleratedStep (n % 2^(k+1))) k := by
          rw [← ih (acceleratedStep (n % 2^(k+1)))]
    rw [htails]

/-- Distinct residues below `2^k` give distinct parity vectors. -/
theorem parityVector_injective_mod_pow_two (k : Nat) (a b : Nat) (ha : a < 2^k) (hb : b < 2^k) :
    parityVector a k = parityVector b k → a = b := by
  induction k generalizing a b with
  | zero =>
    intro _
    have ha0 : a = 0 := by
      have : a < 1 := by simpa using ha
      omega
    have hb0 : b = 0 := by
      have : b < 1 := by simpa using hb
      omega
    rw [ha0, hb0]
  | succ k ih =>
    intro hpv
    rw [parityVector_succ a k, parityVector_succ b k] at hpv
    injection hpv with hhead htail
    by_cases heven : a % 2 = 0
    · -- a even, so b even
      have hb_even : b % 2 = 0 := by omega
      have hsa : acceleratedStep a = a / 2 := by simp [acceleratedStep, heven]
      have hsb : acceleratedStep b = b / 2 := by simp [acceleratedStep, hb_even]
      rw [hsa, hsb] at htail
      have ha2 : a / 2 < 2^k := by
        have : a < 2 * (2^k) := by
          rw [show 2 * (2^k) = 2^(k+1) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
          exact ha
        omega
      have hb2 : b / 2 < 2^k := by
        have : b < 2 * (2^k) := by
          rw [show 2 * (2^k) = 2^(k+1) by rw [Nat.pow_succ]; rw [Nat.mul_comm]]
          exact hb
        omega
      have hab2 : a / 2 = b / 2 := ih (a / 2) (b / 2) ha2 hb2 htail
      have ha_eq : a = 2 * (a / 2) := by
        rw [← Nat.div_add_mod a 2, heven]
        omega
      have hb_eq : b = 2 * (b / 2) := by
        rw [← Nat.div_add_mod b 2, hb_even]
        omega
      have : a = b := by
        rw [ha_eq, hb_eq, hab2]
      exact this
    · -- a odd, so b odd
      have hodd : a % 2 = 1 := by omega
      have hb_odd : b % 2 = 1 := by omega
      have hsa : acceleratedStep a = (3 * a + 1) / 2 := by simp [acceleratedStep, hodd]
      have hsb : acceleratedStep b = (3 * b + 1) / 2 := by simp [acceleratedStep, hb_odd]
      rw [hsa, hsb] at htail
      have htail' : parityVector ((3 * a + 1) / 2 % 2^k) k = parityVector ((3 * b + 1) / 2 % 2^k) k := by
        rw [← parityVector_mod_pow_two ((3 * a + 1) / 2) k]
        rw [← parityVector_mod_pow_two ((3 * b + 1) / 2) k]
        exact htail
      have ha2 : (3 * a + 1) / 2 % 2^k < 2^k := by
        apply Nat.mod_lt
        apply two_pow_pos
      have hb2 : (3 * b + 1) / 2 % 2^k < 2^k := by
        apply Nat.mod_lt
        apply two_pow_pos
      have hab2 : (3 * a + 1) / 2 % 2^k = (3 * b + 1) / 2 % 2^k := ih _ _ ha2 hb2 htail'
      have h3a1 : (3 * a + 1) % 2 = 0 := by omega
      have h3b1 : (3 * b + 1) % 2 = 0 := by omega
      have hmod : (3 * a + 1) % 2^(k+1) = (3 * b + 1) % 2^(k+1) := by
        apply mod_pow_succ_of_div_two_mod h3a1 h3b1
        exact hab2
      have h3ab : 3 * a % 2^(k+1) = 3 * b % 2^(k+1) := by
        apply add_mod_cancel_right _ _ 1 _
        exact hmod
      have h_ab_mod : a % 2^(k+1) = b % 2^(k+1) := by
        apply mul_three_cancel_mod_pow_two (k + 1) a b
        exact h3ab
      have ha' : a % 2^(k+1) = a := by
        apply Nat.mod_eq_of_lt
        exact ha
      have hb' : b % 2^(k+1) = b := by
        apply Nat.mod_eq_of_lt
        exact hb
      rw [ha', hb'] at h_ab_mod
      exact h_ab_mod

/-- Every length-k {0,1}-pattern occurs as a parity vector. -/
theorem parityVector_surjective_mod_pow_two (k : Nat) (p : List Nat) (hp : p.length = k)
    (hpval : ∀ x ∈ p, x = 0 ∨ x = 1) : ∃ a : Nat, a < 2^k ∧ parityVector a k = p := by
  induction k generalizing p with
  | zero =>
    have hp_empty : p = [] := by
      rw [List.eq_nil_iff_length_eq_zero, hp]
    refine ⟨0, ⟨?_, ?_⟩⟩
    · simp
    · simp [parityVector, hp_empty]
  | succ k ih =>
    cases p with
    | nil =>
      exfalso
      simp at hp
    | cons b q =>
      have hb : b = 0 ∨ b = 1 := hpval b (by simp)
      have hqval : ∀ x ∈ q, x = 0 ∨ x = 1 := by
        intro x hx
        exact hpval x (by simp [hx])
      have hq_len : q.length = k := by
        simp at hp
        exact hp
      have ih_q : ∃ a < 2^k, parityVector a k = q := ih q hq_len hqval
      cases ih_q with | intro a ha_eq =>
      cases ha_eq with | intro ha hq_a =>
      cases hb with
      | inl hb0 =>
        refine ⟨2 * a, ⟨?_, ?_⟩⟩
        · rw [Nat.pow_succ]
          omega
        · rw [parityVector_succ (2 * a) k]
          have h1 : 2 * a % 2 = 0 := by
            omega
          have h2 : acceleratedStep (2 * a) = a := by
            simp [acceleratedStep]
          rw [h1, h2, hb0, hq_a]
      | inr hb1 =>
        let u := inv3Mod k
        let m := (u * (a + 2^(k+1) - 2)) % 2^k
        refine ⟨2 * m + 1, ⟨?_, ?_⟩⟩
        · have hm : m < 2^k := by
            apply Nat.mod_lt
            apply two_pow_pos
          rw [Nat.pow_succ]
          omega
        · rw [parityVector_succ (2 * m + 1) k]
          have h1 : (2 * m + 1) % 2 = 1 := by
            omega
          have h2 : acceleratedStep (2 * m + 1) = 3 * m + 2 := by
            simp [acceleratedStep]
            omega
          rw [h1, h2]
          have h3 : parityVector (3 * m + 2) k = parityVector ((3 * m + 2) % 2^k) k := by
            apply parityVector_mod_pow_two
          have h4 : (3 * m + 2) % 2^k = a := by
            have h5 : 3 * m % 2^k = (a + 2^(k+1) - 2) % 2^k := by
              have eq1 : 3 * m % 2^k = 3 * ((u * (a + 2^(k+1) - 2)) % 2^k) % 2^k := rfl
              rw [eq1]
              apply mul_mod_of_inv
              exact inv3Mod_spec k
            calc
              (3 * m + 2) % 2^k
                = (3 * m % 2^k + 2 % 2^k) % 2^k := by rw [Nat.add_mod]
              _ = ((a + 2^(k+1) - 2) % 2^k + 2 % 2^k) % 2^k := by rw [h5]
              _ = (a + 2^(k+1) - 2 + 2) % 2^k := by rw [← Nat.add_mod]
              _ = (a + 2^(k+1)) % 2^k := by
                have hsub : a + 2^(k+1) - 2 + 2 = a + 2^(k+1) := by
                  omega
                rw [hsub]
              _ = a % 2^k := by
                have hdiv : 2^k ∣ 2^(k+1) := by
                  refine ⟨2, ?_⟩
                  rw [Nat.pow_succ]
                have heq : (a + 2^(k+1)) % 2^k = a % 2^k := by
                  apply add_multiple_mod_eq
                  exact hdiv
                exact heq
              _ = a := by
                apply Nat.mod_eq_of_lt
                exact ha
          rw [h3, h4, hq_a, hb1]

end parity_vectors

end Collatz
