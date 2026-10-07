import Collatz.Exploration.GapEndpointCertificates

/-! Sequential endpoint checking with carried powers, evaluated by the Lean kernel. -/
namespace Collatz.Exploration.GapEndpointScan
open GapEndpointCertificates

def scan (N : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | R+1, a, C, D =>
    if C*3 < D*2 then
      decide (D*2 ≤ C*3*3 ∧ (a+1)*(C*3) < 3*(D*2-C*3)*N) &&
        scan N R (a+1) (C*3) (D*2)
    else
      decide (D*2 ≤ C*3 ∧ a*C < 3*(D*2-C)*N) &&
        scan N R a C (D*2)

def Endpoint (N j : Nat) : Prop :=
  ∃ A, 2^j ≤ 3^(A+1) ∧ A*3^A < 3*(2^j-3^A)*N

/-- A true scan certifies every endpoint in its explicitly finite interval. -/
theorem scan_sound (N R : Nat) : ∀ a C D j : Nat,
    C=3^a → D=2^j → scan N R a C D=true →
    ∀ t, t<R → Endpoint N (j+t+1) := by
  induction R with
  | zero => intro a C D j hC hD hs t ht; omega
  | succ R ih =>
    intro a C D j hC hD hs t ht
    have hD' : D*2=2^(j+1) := by rw [Nat.pow_succ]; rw [hD]
    by_cases h : C*3<D*2
    · simp only [scan,if_pos h,Bool.and_eq_true,decide_eq_true_eq] at hs
      have hC' : C*3=3^(a+1) := by rw [Nat.pow_succ]; rw [hC]
      cases t with
      | zero =>
        refine ⟨a+1,?_,?_⟩
        · simpa only [Nat.add_zero,hD',hC',Nat.pow_succ] using hs.1.1
        · simpa only [Nat.add_zero,hD',hC'] using hs.1.2
      | succ t =>
        have hz := ih (a+1) (C*3) (D*2) (j+1) hC' hD' hs.2 t (by omega)
        have he : j+(t+1)+1=(j+1)+t+1 := by omega
        rw [he]
        exact hz
    · simp only [scan,if_neg h,Bool.and_eq_true,decide_eq_true_eq] at hs
      cases t with
      | zero =>
        refine ⟨a,?_,?_⟩
        · simpa only [Nat.add_zero,hD',hC,Nat.pow_succ] using hs.1.1
        · simpa only [Nat.add_zero,hD',hC] using hs.1.2
      | succ t =>
        have hz := ih a C (D*2) (j+1) hC hD' hs.2 t (by omega)
        have he : j+(t+1)+1=(j+1)+t+1 := by omega
        rw [he]
        exact hz

/-- Certified scanning supplies a finite first-light theorem for every source above N. -/
theorem first_light_of_scan {N H n j : Nat} (hs : scan N H 0 1 1=true)
    (hn : N ≤ n) (hj : j ≤ H) (hf : FirstLightDescent.FirstLight n j) :
    acceleratedOrbit j n < n := by
  cases j with
  | zero => have hh := hf.1; simp at hh
  | succ j =>
    have he := scan_sound N H 0 1 1 0 (by simp) (by simp) hs j (by omega)
    simp only [Nat.zero_add] at he
    obtain ⟨A,hcap,hgap⟩ := he
    exact first_light_descent hf (odd_cap hf.1 hcap) hn hgap

end Collatz.Exploration.GapEndpointScan
