import Collatz.Basic

/-!
# Unconstrained increments

An increment `d` gives the step `n ↦ n/2` (even) or `n ↦ 3n+d` (odd).
Collatz is the case `d = 1`.  This file proves that some *odd* `d`,
depending on the start, always reaches `1`, and records the elementary
distinctions between `d = 0` (the map `n ↦ 3n` on odds), `d = 1`, `d = 5`,
and `d = 7`.

None of this is a proof of the Collatz conjecture.  The conjecture is the
statement that the *same* increment `d = 1` works for every positive start.
-/

namespace Collatz
namespace DeviceUnconstrained

/-! ## Incremented step -/

/-- The Collatz step with additive constant `d` on the odd branch. -/
def stepInc (d n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then n / 2
  else 3 * n + d

/-- Iteration of `stepInc d`. -/
def orbitInc (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbitInc d k (stepInc d n)

@[simp] theorem orbitInc_zero (d n : Nat) : orbitInc d 0 n = n := rfl

@[simp] theorem orbitInc_succ (d k n : Nat) :
    orbitInc d (k + 1) n = orbitInc d k (stepInc d n) := rfl

/-- The ordinary Collatz step is increment `1`. -/
theorem stepInc_one (n : Nat) : stepInc 1 n = step n := by
  simp [stepInc, step]

/-- Iterates agree when the increment is `1`. -/
theorem orbitInc_one (k n : Nat) : orbitInc 1 k n = orbit k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [orbitInc_succ, orbit_succ_steps, stepInc_one, ih]

/-- An unconstrained certificate: some odd positive increment reaches `1`. -/
def UnconstrainedCertificate (n : Nat) : Prop :=
  ∃ d t : Nat, 0 < d ∧ d % 2 = 1 ∧ orbitInc d t n = 1

/-- A Collatz certificate is the constrained increment `1`. -/
def CollatzCertificate (n : Nat) : Prop :=
  ∃ t : Nat, orbit t n = 1

/-! ## Parity of the incremented step -/

theorem stepInc_even {d n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    stepInc d n = n / 2 := by
  have h0 : n ≠ 0 := by omega
  simp [stepInc, h0, he]

theorem stepInc_odd {d n : Nat} (ho : n % 2 = 1) :
    stepInc d n = 3 * n + d := by
  have h0 : n ≠ 0 := by omega
  have hne : n % 2 ≠ 0 := by omega
  simp [stepInc, h0, hne]

theorem stepInc_two_mul {d n : Nat} (hn : 0 < n) :
    stepInc d (2 * n) = n := by
  have hpos : 0 < 2 * n := by omega
  have he : (2 * n) % 2 = 0 := by omega
  rw [stepInc_even hpos he]
  omega

theorem two_pow_succ_even (k : Nat) : 2 ^ (k + 1) % 2 = 0 := by
  rw [Nat.pow_succ]
  omega

theorem two_pow_ge_one_even {k : Nat} (hk : 1 ≤ k) : 2 ^ k % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k => exact two_pow_succ_even k

/-! ## Ordinary step lemmas, from `Basic` -/

theorem step_even {n : Nat} (hn : 0 < n) (he : n % 2 = 0) : step n = n / 2 := by
  have h0 : n ≠ 0 := by omega
  simp [step, h0, he]

theorem step_odd {n : Nat} (ho : n % 2 = 1) : step n = 3 * n + 1 := by
  have h0 : n ≠ 0 := by omega
  have hne : n % 2 ≠ 0 := by omega
  simp [step, h0, hne]

/-! ## Powers of two reach `1` by halving -/

theorem exists_two_pow_gt (n : Nat) : ∃ k : Nat, n < 2 ^ k := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    have hle : n + 1 ≤ 2 ^ k := Nat.succ_le_of_lt hk
    have hlt : 2 ^ k < 2 ^ (k + 1) := by
      rw [Nat.pow_succ]
      have : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    omega

theorem two_pow_ge_two_of_gt_one {K n : Nat} (hn : 1 ≤ n) (h : 3 * n < 2 ^ K) :
    2 ≤ K := by
  have h3 : 3 ≤ 3 * n := by omega
  have hlt : 3 < 2 ^ K := Nat.lt_of_le_of_lt h3 h
  cases K with
  | zero =>
    simp at hlt
  | succ K' =>
    cases K' with
    | zero =>
      simp at hlt
    | succ K'' =>
      omega

theorem orbitInc_two_pow (d k : Nat) : orbitInc d k (2 ^ k) = 1 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    have he : 2 ^ (k + 1) % 2 = 0 := two_pow_succ_even k
    rw [orbitInc_succ, stepInc_even hpos he]
    have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
      rw [Nat.pow_succ]
      omega
    rw [hdiv, ih]

theorem orbit_two_pow (k : Nat) : orbit k (2 ^ k) = 1 := by
  rw [← orbitInc_one]
  exact orbitInc_two_pow 1 k

/-! ## One-shot odd increment: land on a power of two -/

theorem one_shot_odd {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    ∃ k d : Nat, 0 < d ∧ d % 2 = 1 ∧ stepInc d n = 2 ^ k := by
  obtain ⟨K, hK⟩ := exists_two_pow_gt (3 * n)
  have hK2 : 2 ≤ K := two_pow_ge_two_of_gt_one (by omega) hK
  have hK1 : 1 ≤ K := by omega
  let d := 2 ^ K - 3 * n
  have hdpos : 0 < d := by
    simp [d]
    omega
  have hsum : 3 * n + d = 2 ^ K := by
    simp [d]
    omega
  have hde : d % 2 = 1 := by
    have heven : 2 ^ K % 2 = 0 := two_pow_ge_one_even hK1
    have hodd : (3 * n) % 2 = 1 := by omega
    have hmod : (3 * n + d) % 2 = 0 := by rw [hsum]; exact heven
    rw [Nat.add_mod] at hmod
    omega
  refine ⟨K, d, hdpos, hde, ?_⟩
  rw [stepInc_odd ho, hsum]

/-- Every odd positive integer has an unconstrained certificate. -/
theorem unconstrained_of_odd {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    UnconstrainedCertificate n := by
  obtain ⟨k, d, hd, hdo, hs⟩ := one_shot_odd hn ho
  refine ⟨d, k + 1, hd, hdo, ?_⟩
  rw [orbitInc_succ, hs, orbitInc_two_pow]

theorem orbitInc_commute (d k n : Nat) :
    orbitInc d k (stepInc d n) = stepInc d (orbitInc d k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [orbitInc_succ, orbitInc_succ]
    exact ih (stepInc d n)

/-- Every positive integer has an unconstrained certificate. -/
theorem unconstrained_exists (n : Nat) (hn : 0 < n) :
    UnconstrainedCertificate n := by
  revert hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases ho : n % 2 = 1
    · exact unconstrained_of_odd hn ho
    · have he : n % 2 = 0 := by omega
      have hn2 : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      obtain ⟨d, t, hd, hdo, hor⟩ := ih (n / 2) hlt hn2
      refine ⟨d, t + 1, hd, hdo, ?_⟩
      rw [orbitInc_succ, stepInc_even hn he, hor]

/-! ## Collatz is uniform increment `1` -/

theorem collatz_certificate_iff {n : Nat} :
    CollatzCertificate n ↔ ∃ t : Nat, orbitInc 1 t n = 1 := by
  constructor
  · intro ⟨t, ht⟩
    exact ⟨t, orbitInc_one t n ▸ ht⟩
  · intro ⟨t, ht⟩
    exact ⟨t, orbitInc_one t n ▸ ht⟩

/-- The Collatz conjecture is: every positive integer has a certificate
with increment `1`.  This is a restatement, not a proof. -/
theorem collatz_iff_uniform_one :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → CollatzCertificate n := by
  constructor
  · intro h n hn
    exact h n hn
  · intro h n hn
    exact h n hn

/-- Straightening: if every unconstrained certificate can be replaced by
increment `1`, Collatz follows.  The hypothesis is not proved. -/
theorem collatz_of_straightening
    (h : ∀ n : Nat, 0 < n → UnconstrainedCertificate n → CollatzCertificate n) :
    CollatzConjecture := by
  intro n hn
  exact h n hn (unconstrained_exists n hn)

/-! ## Kernel identities for the folded odd branch -/

/-- Folded odd branch for increment `d`. -/
def foldInc (d n : Nat) : Nat := (3 * n + d) / 2

theorem odd_add_odd_even {n d : Nat} (ho : n % 2 = 1) (hd : d % 2 = 1) :
    (3 * n + d) % 2 = 0 := by omega

theorem fold_mul_two {d n : Nat} (ho : n % 2 = 1) (hd : d % 2 = 1) :
    2 * foldInc d n = 3 * n + d := by
  have : (3 * n + d) % 2 = 0 := odd_add_odd_even ho hd
  simp [foldInc]
  omega

/-- An odd `3n+1` step multiplies the kernel `n+1` by `3/2`. -/
theorem kernel_fold_one {n : Nat} (ho : n % 2 = 1) :
    2 * (foldInc 1 n + 1) = 3 * (n + 1) := by
  have hd : (1 : Nat) % 2 = 1 := by decide
  have h2 : 2 * foldInc 1 n = 3 * n + 1 := fold_mul_two ho hd
  omega

/-- The same identity for increment `5`, with kernel `n+5`. -/
theorem kernel_fold_five {n : Nat} (ho : n % 2 = 1) :
    2 * (foldInc 5 n + 5) = 3 * (n + 5) := by
  have hd : (5 : Nat) % 2 = 1 := by decide
  have h2 : 2 * foldInc 5 n = 3 * n + 5 := fold_mul_two ho hd
  omega

/-- The same identity for increment `7`, with kernel `n+7`. -/
theorem kernel_fold_seven {n : Nat} (ho : n % 2 = 1) :
    2 * (foldInc 7 n + 7) = 3 * (n + 7) := by
  have hd : (7 : Nat) % 2 = 1 := by decide
  have h2 : 2 * foldInc 7 n = 3 * n + 7 := fold_mul_two ho hd
  omega

theorem kernel_one_at_one : 1 + 1 = 2 := rfl
theorem kernel_five_at_one : 1 + 5 = 6 := rfl
theorem kernel_seven_at_one : 1 + 7 = 8 := rfl

/-! ## Why `3n` fails: even increment, odd stays odd -/

theorem even_inc_keeps_odd {d n : Nat} (hd : d % 2 = 0) (ho : n % 2 = 1) :
    (3 * n + d) % 2 = 1 := by omega

theorem triple_keeps_odd {n : Nat} (ho : n % 2 = 1) : (3 * n) % 2 = 1 := by
  omega

theorem stepInc_zero_odd {n : Nat} (ho : n % 2 = 1) :
    stepInc 0 n = 3 * n := by
  rw [stepInc_odd ho]
  omega

theorem triple_grows {n : Nat} (hn : 1 < n) : n < 3 * n := by omega

/-- Under increment `0`, an odd start larger than `1` stays odd and strictly
increases, so it never meets `1`. -/
theorem triple_never_one {n : Nat} (hn : 1 < n) (ho : n % 2 = 1) (k : Nat) :
    orbitInc 0 k n ≠ 1 := by
  induction k generalizing n with
  | zero =>
    simp
    omega
  | succ k ih =>
    have hpos : 0 < n := by omega
    rw [orbitInc_succ, stepInc_zero_odd ho]
    have h3 : 1 < 3 * n := by omega
    have ho3 : (3 * n) % 2 = 1 := triple_keeps_odd ho
    exact ih h3 ho3

/-- `3` does not reach `1` under `n ↦ 3n` on odds. -/
theorem three_not_certificate_zero : ¬ ∃ t : Nat, orbitInc 0 t 3 = 1 := by
  intro ⟨t, ht⟩
  exact triple_never_one (n := 3) (by decide) (by decide) t ht

/-! ## The tautological cycle of an odd increment -/

theorem tautological_odd {d : Nat} (hd : d % 2 = 1) :
    stepInc d d = 4 * d := by
  have hpos : 0 < d := by omega
  rw [stepInc_odd hd]
  omega

theorem tautological_four {d : Nat} (hpos : 0 < d) :
    stepInc d (4 * d) = 2 * d := by
  have h4 : 0 < 4 * d := by omega
  have he : (4 * d) % 2 = 0 := by omega
  rw [stepInc_even h4 he]
  omega

theorem tautological_two {d : Nat} (hpos : 0 < d) :
    stepInc d (2 * d) = d := by
  have h2 : 0 < 2 * d := by omega
  have he : (2 * d) % 2 = 0 := by omega
  rw [stepInc_even h2 he]
  omega

/-- For every odd positive `d`, the orbit of `d` is the 3-cycle
`d, 4d, 2d`. -/
theorem tautological_cycle {d : Nat} (hd : d % 2 = 1) (hpos : 0 < d) :
    orbitInc d 3 d = d := by
  rw [orbitInc_succ, tautological_odd hd]
  rw [orbitInc_succ, tautological_four hpos]
  rw [orbitInc_succ, tautological_two hpos]
  rfl

/-- `1` lies on the tautological cycle if and only if `d = 1`. -/
theorem one_on_tautological_iff {d : Nat} (_hd : d % 2 = 1) (_hpos : 0 < d) :
    (d = 1 ∨ 2 * d = 1 ∨ 4 * d = 1) ↔ d = 1 := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact h
    · omega
    · omega
  · intro h
    exact Or.inl h

/-- The first odd step from `1` joins the tautological cycle iff `d = 1`. -/
theorem one_joins_tautological_iff {d : Nat} (_hd : d % 2 = 1) (_hpos : 0 < d) :
    stepInc d 1 = 4 * d ↔ d = 1 := by
  have ho : (1 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]
  constructor
  · intro h
    omega
  · intro h
    omega

/-! ## Increment `5`: the tautological cycle misses `1` -/

theorem stepInc_five_five : stepInc 5 5 = 20 := by
  have ho : (5 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem stepInc_five_twenty : stepInc 5 20 = 10 := by
  have hn : 0 < (20 : Nat) := by decide
  have he : (20 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_five_ten : stepInc 5 10 = 5 := by
  have hn : 0 < (10 : Nat) := by decide
  have he : (10 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

def InFiveCycle (n : Nat) : Prop := n = 5 ∨ n = 10 ∨ n = 20

theorem stepInc_five_cycle {n : Nat} (h : InFiveCycle n) :
    InFiveCycle (stepInc 5 n) := by
  rcases h with h | h | h
  · rw [h, stepInc_five_five]
    exact Or.inr (Or.inr rfl)
  · rw [h, stepInc_five_ten]
    exact Or.inl rfl
  · rw [h, stepInc_five_twenty]
    exact Or.inr (Or.inl rfl)

theorem orbitInc_five_cycle (k : Nat) : InFiveCycle (orbitInc 5 k 5) := by
  induction k with
  | zero =>
    simp [InFiveCycle]
  | succ k ih =>
    rw [orbitInc_succ, orbitInc_commute]
    exact stepInc_five_cycle ih

theorem one_not_five_cycle : ¬ InFiveCycle 1 := by
  intro h
  rcases h with h | h | h <;> omega

/-- `5` never reaches `1` under `3n+5`. -/
theorem five_not_reach_one_inc5 (k : Nat) : orbitInc 5 k 5 ≠ 1 := by
  intro h
  have hc := orbitInc_five_cycle k
  rw [h] at hc
  exact one_not_five_cycle hc

/-! ## Increment `7`: the tautological cycle misses `1` -/

theorem stepInc_seven_seven : stepInc 7 7 = 28 := by
  have ho : (7 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem stepInc_seven_twentyeight : stepInc 7 28 = 14 := by
  have hn : 0 < (28 : Nat) := by decide
  have he : (28 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_seven_fourteen : stepInc 7 14 = 7 := by
  have hn : 0 < (14 : Nat) := by decide
  have he : (14 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

def InSevenCycle (n : Nat) : Prop := n = 7 ∨ n = 14 ∨ n = 28

theorem stepInc_seven_cycle {n : Nat} (h : InSevenCycle n) :
    InSevenCycle (stepInc 7 n) := by
  rcases h with h | h | h
  · rw [h, stepInc_seven_seven]
    exact Or.inr (Or.inr rfl)
  · rw [h, stepInc_seven_fourteen]
    exact Or.inl rfl
  · rw [h, stepInc_seven_twentyeight]
    exact Or.inr (Or.inl rfl)

theorem orbitInc_seven_cycle (k : Nat) : InSevenCycle (orbitInc 7 k 7) := by
  induction k with
  | zero =>
    simp [InSevenCycle]
  | succ k ih =>
    rw [orbitInc_succ, orbitInc_commute]
    exact stepInc_seven_cycle ih

theorem one_not_seven_cycle : ¬ InSevenCycle 1 := by
  intro h
  rcases h with h | h | h <;> omega

/-- `7` never reaches `1` under `3n+7`. -/
theorem seven_not_reach_one_inc7 (k : Nat) : orbitInc 7 k 7 ≠ 1 := by
  intro h
  have hc := orbitInc_seven_cycle k
  rw [h] at hc
  exact one_not_seven_cycle hc

/-! The 6-cycle that `1` falls into under increment `7`. -/

def InSevenSixCycle (n : Nat) : Prop :=
  n = 5 ∨ n = 10 ∨ n = 11 ∨ n = 20 ∨ n = 22 ∨ n = 40

theorem stepInc_seven_five : stepInc 7 5 = 22 := by
  have ho : (5 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem stepInc_seven_twentytwo : stepInc 7 22 = 11 := by
  have hn : 0 < (22 : Nat) := by decide
  have he : (22 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_seven_eleven : stepInc 7 11 = 40 := by
  have ho : (11 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem stepInc_seven_forty : stepInc 7 40 = 20 := by
  have hn : 0 < (40 : Nat) := by decide
  have he : (40 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_seven_twenty : stepInc 7 20 = 10 := by
  have hn : 0 < (20 : Nat) := by decide
  have he : (20 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_seven_ten : stepInc 7 10 = 5 := by
  have hn : 0 < (10 : Nat) := by decide
  have he : (10 : Nat) % 2 = 0 := by decide
  rw [stepInc_even hn he]

theorem stepInc_seven_six_cycle {n : Nat} (h : InSevenSixCycle n) :
    InSevenSixCycle (stepInc 7 n) := by
  rcases h with h | h | h | h | h | h
  · rw [h, stepInc_seven_five]; simp [InSevenSixCycle]
  · rw [h, stepInc_seven_ten]; simp [InSevenSixCycle]
  · rw [h, stepInc_seven_eleven]; simp [InSevenSixCycle]
  · rw [h, stepInc_seven_twenty]; simp [InSevenSixCycle]
  · rw [h, stepInc_seven_twentytwo]; simp [InSevenSixCycle]
  · rw [h, stepInc_seven_forty]; simp [InSevenSixCycle]

theorem stepInc_seven_one : stepInc 7 1 = 10 := by
  have ho : (1 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem orbitInc_from_ten (k : Nat) : InSevenSixCycle (orbitInc 7 k 10) := by
  induction k with
  | zero =>
    simp [InSevenSixCycle]
  | succ k ih =>
    rw [orbitInc_succ, orbitInc_commute]
    exact stepInc_seven_six_cycle ih

theorem orbitInc_seven_one_succ (k : Nat) :
    InSevenSixCycle (orbitInc 7 (k + 1) 1) := by
  rw [orbitInc_succ, stepInc_seven_one]
  exact orbitInc_from_ten k

/-- After at least one step, the orbit of `1` under `3n+7` lies in a 6-cycle
that does not contain `1`. -/
theorem one_leaves_under_seven {k : Nat} (hk : 0 < k) :
    orbitInc 7 k 1 ≠ 1 := by
  cases k with
  | zero => omega
  | succ k =>
    intro h
    have hc := orbitInc_seven_one_succ k
    rw [h] at hc
    rcases hc with h' | h' | h' | h' | h' | h' <;> omega

/-! ## Sample one-shot increments -/

theorem one_shot_at_one : stepInc 1 1 = 2 ^ 2 := by
  have ho : (1 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem one_shot_at_five : stepInc 1 5 = 2 ^ 4 := by
  have ho : (5 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

theorem one_shot_at_seven : stepInc 11 7 = 2 ^ 5 := by
  have ho : (7 : Nat) % 2 = 1 := by decide
  rw [stepInc_odd ho]

end DeviceUnconstrained
end Collatz
