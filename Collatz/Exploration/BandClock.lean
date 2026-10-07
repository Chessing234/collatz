import Collatz.Exploration.BarrierKernel

/-! Consequences of a proved fixed-barrier exit clock. The abstraction preserves
both exit directions and gives finite-prefix witness counts at rational thresholds. -/
namespace Collatz.Exploration.BandClock
open BarrierKernel

def ExitClock (P Q K : Nat) : Prop :=
  ∀ b n : Nat, 1 < b → ∃ k, k ≤ K ∧ (orbit k n < b ∨ P*b < Q*orbit k n)

/-- A proved clock transfers to every narrower positive-denominator band. -/
theorem narrower_ratio {P Q A B K : Nat} (hc : ExitClock P Q K)
    (hB : 0 < B) (hcross : A*Q ≤ P*B) : ExitClock A B K := by
  intro b n hb
  obtain ⟨k,hk,hl | hu⟩ := hc b n hb
  · exact ⟨k,hk,Or.inl hl⟩
  · refine ⟨k,hk,Or.inr ?_⟩
    have hm : Q*(A*b) < Q*(B*orbit k n) := calc
      Q*(A*b) = (A*Q)*b := by ac_rfl
      _ ≤ (P*B)*b := Nat.mul_le_mul_right b hcross
      _ = B*(P*b) := by ac_rfl
      _ < B*(Q*orbit k n) := Nat.mul_lt_mul_of_pos_left hu hB
      _ = Q*(B*orbit k n) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hm

theorem no_band_through {P Q K b n : Nat} (hc : ExitClock P Q K) (hb : 1 < b)
    (h : ∀ k, k ≤ K → b ≤ orbit k n ∧ Q*orbit k n ≤ P*b) : False := by
  obtain ⟨k,hk,hl | hu⟩ := hc b n hb
  · have := h k hk; omega
  · have := h k hk; omega

theorem high_within {P Q K b n : Nat} (hc : ExitClock P Q K) (hb : 1 < b)
    (h : Kernel b n) : ∃ k, k ≤ K ∧ P*b < Q*orbit k n := by
  obtain ⟨k,hk,hl | hu⟩ := hc b n hb
  · have := h k; omega
  · exact ⟨k,hk,hu⟩

theorem high_window {P Q K b n : Nat} (hc : ExitClock P Q K) (hb : 1 < b)
    (h : Kernel b n) (t : Nat) :
    ∃ s, t ≤ s ∧ s ≤ t+K ∧ P*b < Q*orbit s n := by
  obtain ⟨k,hk,hv⟩ := high_within hc hb (kernel_forward h t)
  refine ⟨k+t,by omega,by omega,?_⟩
  rw [orbit_add]
  exact hv

/-- One distinct high time in each complete (K+1)-point block, using only
lower survival of the observed prefix. N=0 gives the empty witness family. -/
theorem finite_survival_witnesses {P Q K b n : Nat} (hc : ExitClock P Q K)
    (hb : 1 < b) (N : Nat) (h : Survives b ((K+1)*N-1) n) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < (K+1)*N ∧ P*b < Q*orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) := by
  classical
  have span (q : Fin N) : (K+1)*(q.val+1) ≤ (K+1)*N :=
    Nat.mul_le_mul_left (K+1) (by have := q.isLt; omega)
  have hw (q : Fin N) : ∃ s,
      (K+1)*q.val ≤ s ∧ s < (K+1)*(q.val+1) ∧ P*b < Q*orbit s n := by
    have hs := span q
    rw [Nat.mul_add, Nat.mul_one] at hs
    obtain ⟨k,hk,hl | hu⟩ := hc b (orbit ((K+1)*q.val) n) hb
    · have hlower := h (k+(K+1)*q.val) (by omega)
      rw [orbit_add] at hlower
      omega
    · refine ⟨k+(K+1)*q.val,by omega,?_,?_⟩
      · rw [Nat.mul_add, Nat.mul_one]; omega
      · rw [orbit_add]; exact hu
  let f (q : Fin N) := Classical.choose (hw q)
  have hf (q : Fin N) :
      (K+1)*q.val ≤ f q ∧ f q < (K+1)*(q.val+1) ∧ P*b < Q*orbit (f q) n :=
    Classical.choose_spec (hw q)
  refine ⟨f,?_,?_⟩
  · intro q
    exact ⟨Nat.lt_of_lt_of_le (hf q).2.1 (span q), (hf q).2.2⟩
  · intro a c he
    have hv : a.val = c.val := by
      by_cases hac : a.val < c.val
      · have hm := Nat.mul_le_mul_left (K+1) (show a.val+1 ≤ c.val by omega)
        have ht := Nat.lt_of_lt_of_le (hf a).2.1 (Nat.le_trans hm (hf c).1)
        omega
      · by_cases hca : c.val < a.val
        · have hm := Nat.mul_le_mul_left (K+1) (show c.val+1 ≤ a.val by omega)
          have ht := Nat.lt_of_lt_of_le (hf c).2.1 (Nat.le_trans hm (hf a).1)
          omega
        · omega
    exact Fin.ext hv

theorem kernel_finite_witnesses {P Q K b n : Nat} (hc : ExitClock P Q K)
    (hb : 1 < b) (h : Kernel b n) (N : Nat) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < (K+1)*N ∧ P*b < Q*orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) :=
  finite_survival_witnesses hc hb N (fun k _ => h k)

end Collatz.Exploration.BandClock
