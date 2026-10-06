import Collatz.Structure.NaturalDensity

/-! Finite exceptions and natural density one, with an explicit cutoff.
These results concern ordinary counts, independently of logarithmic density. -/
namespace Collatz.NaturalDensity
open PeriodicCounting

/-- An eventually true predicate misses at most its initial exceptional interval. -/
theorem predicateCount_eventual_lower (P : Nat → Prop) (B N : Nat)
    (h : ∀ n, B≤n → P n) : N ≤ B+predicateCount P N := by
  classical
  by_cases hBN : B≤N
  · have hf : (fun n => decide (P (B+n))) = (fun _ => true) := by
      funext n
      exact decide_eq_true_eq.mpr (h _ (by omega))
    have hc := count_add_shift (fun n => decide (P n)) B (N-B)
    rw [hf, count_full, Nat.add_sub_cancel' hBN] at hc
    change N ≤ B+countBelow (fun n => decide (P n)) N
    omega
  · omega

/-- Quantitative density-one inequality after cutoff q*B. -/
theorem cofinite_precision (P : Nat → Prop) (B q N : Nat)
    (h : ∀ n, B≤n → P n) (hq : 0<q) (hN : q*B≤N) :
    (q-1)*N ≤ q*predicateCount P N := by
  have hl := Nat.mul_le_mul_left q (predicateCount_eventual_lower P B N h)
  rw [Nat.mul_add] at hl
  have he : q*N = (q-1)*N+N := by
    have hq' : q=q-1+1 := by omega
    calc q*N = (q-1+1)*N := congrArg (fun x => x*N) hq'
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Every predicate true beyond a fixed cutoff has natural density one. -/
theorem densityOne_of_eventually {P : Nat → Prop} {B : Nat}
    (h : ∀ n, B≤n → P n) : DensityOne P := by
  intro q hq
  exact ⟨q*B, fun N hn => cofinite_precision P B q N h hq hn⟩

/-- In particular, deleting any initial interval preserves density one. -/
theorem densityOne_tail (B : Nat) : DensityOne (fun n => B≤n) :=
  densityOne_of_eventually (B := B) (fun _ hn => hn)

/-- Natural density one is strictly weaker than universal membership. -/
theorem densityOne_not_universal :
    ∃ P : Nat → Prop, DensityOne P ∧ ¬ (∀ n, P n) := by
  refine ⟨fun n => 1≤n, densityOne_tail 1, ?_⟩
  intro h
  have := h 0
  omega

/-- Eventual inclusion loses at most the size of the initial exceptional interval. -/
theorem predicateCount_eventual_mono {P Q : Nat → Prop} (B N : Nat)
    (h : ∀ n, B≤n → P n → Q n) : predicateCount P N ≤ B+predicateCount Q N := by
  classical
  by_cases hBN : B≤N
  · have he : B+(N-B)=N := by omega
    have hP := count_add_shift (fun n => decide (P n)) B (N-B)
    have hQ := count_add_shift (fun n => decide (Q n)) B (N-B)
    rw [he] at hP hQ
    have hprefix := count_le (fun n => decide (P n)) B
    have htail := count_le_of_imp (fun n => decide (P (B+n)))
      (fun n => decide (Q (B+n))) (N-B) (by
        intro n hn
        exact decide_eq_true_eq.mpr (h _ (by omega) (decide_eq_true_eq.mp hn)))
    change countBelow (fun n => decide (P n)) N ≤ B+countBelow (fun n => decide (Q n)) N
    omega
  · have := predicateCount_le P N
    omega

/-- Density one survives a finite exceptional set in an inclusion argument. -/
theorem densityOne_eventual_mono {P Q : Nat → Prop} {B : Nat}
    (h : ∀ n, B≤n → P n → Q n) (hp : DensityOne P) : DensityOne Q := by
  intro q hq
  obtain ⟨N0, hN⟩ := hp (2*q) (by omega)
  refine ⟨max N0 (2*q*B), ?_⟩
  intro N hn
  have hbase := hN N (by omega)
  have hcounts := Nat.mul_le_mul_left (2*q) (predicateCount_eventual_mono B N h)
  rw [Nat.mul_add] at hcounts
  have hcut : 2*q*B≤N := by omega
  have hexp : 2*q-1 = 2*(q-1)+1 := by omega
  rw [hexp, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hbase
  simp only [Nat.mul_assoc] at hbase hcounts hcut
  omega

/-- Agreement outside a finite initial interval preserves density-one status. -/
theorem densityOne_iff_eventually_equal {P Q : Nat → Prop} {B : Nat}
    (h : ∀ n, B≤n → (P n ↔ Q n)) : DensityOne P ↔ DensityOne Q :=
  ⟨densityOne_eventual_mono (fun n hn => (h n hn).mp),
   densityOne_eventual_mono (fun n hn => (h n hn).mpr)⟩

end Collatz.NaturalDensity
