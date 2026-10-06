import Collatz.Structure.NaturalDensityCounting

/-! Elementary separation tests for natural density one. -/
namespace Collatz.NaturalDensity

/-- The lower-density formulation of density one gives an explicit upper
bound for its complementary count at every precision. -/
theorem complement_precision {P : Nat → Prop} (hP : DensityOne P)
    {q : Nat} (hq : 0<q) : ∃ N0, ∀ N, N0≤N →
      q*predicateCount (fun n => ¬P n) N≤N := by
  obtain ⟨N0, hN⟩ := hP q hq
  refine ⟨N0, ?_⟩
  intro N hn
  have hbase := hN N hn
  have hpart := congrArg (fun x => q*x) (predicateCount_complement P N)
  have hqeq : q=q-1+1 := by omega
  have hsplit : q*N=(q-1)*N+N := by
    calc q*N=(q-1+1)*N := congrArg (fun x => x*N) hqeq
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_add] at hpart
  omega

/-- A positive lower fraction of missing inputs excludes density one. -/
theorem not_densityOne_of_complement_lower {P : Nat → Prop} (C B : Nat)
    (h : ∀ N, B≤N → N≤C*predicateCount (fun n => ¬P n) N) :
    ¬DensityOne P := by
  intro hP
  obtain ⟨N0, hN⟩ := complement_precision hP (q := C+1) (by omega)
  let N := max N0 B+1
  have hu := hN N (by dsimp [N]; omega)
  have hl := h N (by dsimp [N]; omega)
  rw [Nat.add_mul, Nat.one_mul] at hu
  have hzero : predicateCount (fun n => ¬P n) N=0 := by omega
  rw [hzero, Nat.mul_zero] at hl
  dsimp [N] at hl
  omega

/-- Every density-one set meets a set with an eventually positive lower
fraction. This requires a linear count bound, not merely infinitely many
members or a sublinear power bound. -/
theorem exists_common_of_positive_lower {P Q : Nat → Prop}
    (hP : DensityOne P) (C B : Nat)
    (hQ : ∀ N, B≤N → N≤C*predicateCount Q N) : ∃ n, P n ∧ Q n := by
  classical
  by_cases hex : ∃ n, P n ∧ Q n
  · exact hex
  · have hsub : ∀ n, Q n → ¬P n := by
      intro n hq hp
      exact hex ⟨n, hp, hq⟩
    have hnot := not_densityOne_of_complement_lower (P := P) C B (by
      intro N hn
      exact Nat.le_trans (hQ N hn)
        (Nat.mul_le_mul_left C (predicateCount_mono hsub N)))
    exact False.elim (hnot hP)

end Collatz.NaturalDensity
