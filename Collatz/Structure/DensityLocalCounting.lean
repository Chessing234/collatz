import Collatz.Structure.DensitySeparation

/-! Local finite-interval inclusions and complementary density precision. -/
namespace Collatz.NaturalDensity
open PeriodicCounting

/-- Inclusion is only needed inside the interval being counted. The first
M inputs may be exceptions. -/
theorem predicateCount_local_mono (P Q : Nat → Prop) (M N : Nat)
    (h : ∀ n, M≤n → n<N → P n → Q n) :
    predicateCount P N≤M+predicateCount Q N := by
  classical
  revert h
  unfold predicateCount
  induction N with
  | zero => intro _; simp only [count_zero]; omega
  | succ N ih =>
    intro h
    by_cases hn : N<M
    · have hc := count_le (fun n => decide (P n)) (N+1)
      omega
    · have hi := ih (fun n hm hl hp => h n hm (by omega) hp)
      rw [count_succ, count_succ]
      by_cases hp : P N
      · have hq := h N (by omega) (by omega) hp
        simp only [hp, hq, decide_true, ite_true]
        omega
      · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
        omega

/-- Complementary upper bounds at all integer precisions imply density one. -/
theorem densityOne_of_complement_precision {P : Nat → Prop}
    (h : ∀ q, 0<q → ∃ N0, ∀ N, N0≤N →
      q*predicateCount (fun n => ¬P n) N≤N) : DensityOne P := by
  intro q hq
  obtain ⟨N0, hN⟩ := h q hq
  refine ⟨N0, ?_⟩
  intro N hn
  have hp := congrArg (fun x => q*x) (predicateCount_complement P N)
  have he : q*N=(q-1)*N+N := by
    have hsplit : q=q-1+1 := by omega
    calc q*N=(q-1+1)*N := congrArg (fun x => x*N) hsplit
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_add] at hp
  have := hN N hn
  omega

/-- A small prefix plus a sparse periodic exceptional set has small total
count. This arithmetic estimate supports a horizon chosen from the cutoff. -/
theorem prefix_and_period_precision (q M N E F : Nat) (hq : 0<q)
    (hprefix : 2*q*M≤N) (htail : 4*q*E≤M)
    (hcount : F≤M+(N/M+1)*E) : q*F≤N := by
  have hc := Nat.mul_le_mul_left (4*q) hcount
  have hd : (N/M+1)*M≤N+M := by
    have := Nat.div_mul_le_self N M
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have htwice := Nat.mul_le_mul_left 2 hprefix
  have hMN : M≤N := by
    have hl := Nat.mul_le_mul_right M (by omega : 1≤2*q)
    simp only [Nat.one_mul] at hl
    omega
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hc htwice
  have ht' : 4*(q*((N/M+1)*E))≤N+M := by
    calc
      4*(q*((N/M+1)*E)) = (N/M+1)*(4*q*E) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (N/M+1)*M := Nat.mul_le_mul_left _ htail
      _ ≤ N+M := hd
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at ht'
  omega

end Collatz.NaturalDensity
