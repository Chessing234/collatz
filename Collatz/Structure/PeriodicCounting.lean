import Collatz.Accelerated

/-!
# Exact counting of a periodic Boolean predicate

Every cutoff consists of complete periods plus one partial period. These
identities and bounds are finite statements; no asymptotic result is assumed.
They support exact counting of certified finite-horizon stopping-time classes.
-/
namespace Collatz.PeriodicCounting

/-- Count successful inputs in the half-open interval [0,N). -/
def countBelow (P : Nat → Bool) (N : Nat) : Nat :=
  ((List.range N).filter P).length

@[simp] theorem count_zero (P : Nat → Bool) : countBelow P 0 = 0 := rfl

/-- Extending the cutoff adds the membership bit of the new input. -/
theorem count_succ (P : Nat → Bool) (N : Nat) :
    countBelow P (N+1) = countBelow P N + if P N then 1 else 0 := by
  cases h : P N <;> simp [countBelow, List.range_succ, List.filter_append, h]

/-- Cardinality is bounded by the size of the interval being counted. -/
theorem count_le (P : Nat → Bool) (N : Nat) : countBelow P N ≤ N := by
  simpa only [countBelow, List.length_range] using List.length_filter_le P (List.range N)

/-- Counts are monotone in their cutoff. -/
theorem count_mono (P : Nat → Bool) {N M : Nat} (hNM : N≤M) :
    countBelow P N ≤ countBelow P M := by
  induction M with
  | zero => have he : N=0 := by omega
            subst he
            exact Nat.le_refl _
  | succ M ih =>
    by_cases h : N≤M
    · have hr := ih h
      rw [count_succ]
      omega
    · have he : N=M+1 := by omega
      subst he
      exact Nat.le_refl _

/-- A full period followed by a prefix splits into their two counts. -/
theorem count_add_period (P : Nat → Bool) (M N : Nat)
    (hp : ∀ n, P (n+M) = P n) :
    countBelow P (M+N) = countBelow P M + countBelow P N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.add_succ, count_succ, ih, count_succ, Nat.add_comm M N, hp N]
    omega

/-- Exact count of q periods and an arbitrary remaining prefix. -/
theorem count_mul_add (P : Nat → Bool) (M q r : Nat)
    (hp : ∀ n, P (n+M) = P n) :
    countBelow P (q*M+r) = q*countBelow P M + countBelow P r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : (q+1)*M+r = M+(q*M+r) := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [he, count_add_period P M (q*M+r) hp, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Exact quotient-and-remainder formula at every cutoff. -/
theorem count_div_mod (P : Nat → Bool) (M N : Nat)
    (hp : ∀ n, P (n+M) = P n) :
    countBelow P N = (N/M)*countBelow P M + countBelow P (N%M) := by
  have he : (N/M)*M+N%M=N := by
    have h := Nat.mod_add_div N M
    rw [Nat.mul_comm] at h
    omega
  rw [← count_mul_add P M (N/M) (N%M) hp, he]

/-- A partial period contributes between zero and one full period's count. -/
theorem periodic_count_bounds (P : Nat → Bool) (M N : Nat) (hM : 0<M)
    (hp : ∀ n, P (n+M) = P n) :
    (N/M)*countBelow P M ≤ countBelow P N ∧
      countBelow P N ≤ (N/M+1)*countBelow P M := by
  have hr := count_mono P (Nat.le_of_lt (Nat.mod_lt N hM))
  rw [count_div_mod P M N hp]
  constructor
  · omega
  · rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Empty and full predicates check the cutoff convention. -/
theorem count_empty (N : Nat) : countBelow (fun _ => false) N = 0 := by
  simp [countBelow]

theorem count_full (N : Nat) : countBelow (fun _ => true) N = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [count_succ, ih]

/-- Uniform integer error bounds around the period's exact proportion. Dividing
by M*N yields an explicit finite-cutoff density error bound when M,N>0. -/
theorem scaled_count_error (P : Nat → Bool) (M N : Nat) (hM : 0<M)
    (hp : ∀ n, P (n+M)=P n) :
    M*countBelow P N ≤ N*countBelow P M + M*M ∧
      N*countBelow P M ≤ M*countBelow P N + M*M := by
  let A := countBelow P M
  let C := countBelow P N
  let q := N/M
  let r := N%M
  have hA : A≤M := count_le P M
  have hb := periodic_count_bounds P M N hM hp
  have hq : q*M≤N := Nat.div_mul_le_self N M
  have hr : r≤M := Nat.le_of_lt (Nat.mod_lt N hM)
  have he : N=q*M+r := by
    have h := Nat.mod_add_div N M
    simpa only [Nat.mul_comm, Nat.add_comm] using h.symm
  constructor
  · calc
      M*C ≤ M*((q+1)*A) := Nat.mul_le_mul_left M hb.2
      _ = (q*M)*A+M*A := by simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc]
      _ ≤ N*A+M*M := Nat.add_le_add (Nat.mul_le_mul_right A hq)
        (Nat.mul_le_mul_left M hA)
  · have hlow : (q*M)*A ≤ M*C := by
      have h := Nat.mul_le_mul_left M hb.1
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    calc
      N*A = (q*M+r)*A := congrArg (fun x => x*A) he
      _ = (q*M)*A+r*A := Nat.add_mul _ _ _
      _ ≤ M*C+M*M := Nat.add_le_add hlow (Nat.mul_le_mul hr hA)

/-- Explicit convergence to the rational period proportion: for q>0 and
N>0, division by M*N*q gives an error at most 1/q as soon as N≥M*q.
The integer formulation avoids importing a real-analysis library. -/
theorem periodic_density_precision (P : Nat → Bool) (M N q : Nat) (hM : 0<M)
    (hp : ∀ n, P (n+M)=P n) (hN : M*q≤N) :
    (M*countBelow P N)*q ≤ (N*countBelow P M)*q+M*N ∧
    (N*countBelow P M)*q ≤ (M*countBelow P N)*q+M*N := by
  have he := scaled_count_error P M N hM hp
  have hb : (M*M)*q≤M*N := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left M hN
  constructor
  · calc
      (M*countBelow P N)*q ≤ (N*countBelow P M+M*M)*q :=
        Nat.mul_le_mul_right q he.1
      _ = (N*countBelow P M)*q+(M*M)*q := Nat.add_mul _ _ _
      _ ≤ (N*countBelow P M)*q+M*N := Nat.add_le_add_left hb _
  · calc
      (N*countBelow P M)*q ≤ (M*countBelow P N+M*M)*q :=
        Nat.mul_le_mul_right q he.2
      _ = (M*countBelow P N)*q+(M*M)*q := Nat.add_mul _ _ _
      _ ≤ (M*countBelow P N)*q+M*N := Nat.add_le_add_left hb _

end Collatz.PeriodicCounting
