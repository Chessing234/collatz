import Collatz.Structure.NaturalDensity

/-! Converting integer precision into the rational-epsilon form of density one.
The conversion is generic in the counts and also applies to diagonal cutoffs. -/
namespace Collatz.NaturalDensity

/-- Every positive rational error admits a positive integer precision. -/
theorem exists_precision_for_rat (eps : Rat) (heps : 0<eps) :
    ∃ q : Nat, 0<q ∧ 1≤eps*(q:Rat) := by
  let q := eps⁻¹.ceil.toNat+1
  have hceil : eps⁻¹ ≤ (eps⁻¹.ceil.toNat : Rat) := by
    apply Rat.le_trans Rat.le_ceil
    simpa only [Rat.intCast_natCast] using
      Rat.intCast_le_intCast.mpr (Int.self_le_toNat eps⁻¹.ceil)
  have hq : eps⁻¹ ≤ (q:Rat) := Rat.le_trans hceil
    (Rat.natCast_le_natCast.mpr (by simp only [q]; omega))
  have hm := Rat.mul_le_mul_of_nonneg_left hq (Rat.le_of_lt heps)
  rw [Rat.mul_inv_cancel eps (Rat.ne_of_gt heps)] at hm
  exact ⟨q, by simp only [q]; omega, hm⟩

/-- A single integer-precision inequality implies the corresponding rational bound. -/
theorem rat_bound_of_integer_precision {q N C : Nat} (hq : 0<q)
    (hcount : (q-1)*N≤q*C) {eps : Rat} (hepsq : 1≤eps*(q:Rat)) :
    (1-eps)*(N:Rat)≤(C:Rat) := by
  have he : q*N=(q-1)*N+N := by
    have hq' : q=q-1+1 := by omega
    calc q*N = (q-1+1)*N := congrArg (fun x => x*N) hq'
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  have hn : q*N≤q*C+N := by omega
  have hc := Rat.natCast_le_natCast.mpr hn
  simp only [Rat.natCast_add, Rat.natCast_mul] at hc
  have herr := Rat.mul_le_mul_of_nonneg_right hepsq
    (show (0:Rat)≤(N:Rat) from Rat.natCast_nonneg)
  rw [Rat.one_mul] at herr
  have hsum := Rat.le_trans hc ((Rat.add_le_add_left (c := (q:Rat)*(C:Rat))).mpr herr)
  have hfactor : (q:Rat)*(C:Rat)+(eps*(q:Rat))*(N:Rat) =
      (q:Rat)*((C:Rat)+eps*(N:Rat)) := by
    rw [Rat.mul_add]
    congr 1
    rw [Rat.mul_comm eps (q:Rat), Rat.mul_assoc]
  rw [hfactor] at hsum
  have h := Rat.le_of_mul_le_mul_left hsum (Rat.natCast_pos.mpr hq)
  have hout := Rat.le_add_iff_sub_le.mp h
  simpa only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.one_mul, Rat.neg_mul] using hout

/-- The integer-precision density predicate implies every positive rational-epsilon bound. -/
theorem densityOne_rat_bound {P : Nat → Prop} (h : DensityOne P)
    (eps : Rat) (heps : 0<eps) :
    ∃ N0 : Nat, ∀ N : Nat, N0≤N → (1-eps)*(N:Rat)≤(predicateCount P N:Rat) := by
  obtain ⟨q, hq, he⟩ := exists_precision_for_rat eps heps
  obtain ⟨N0, hN⟩ := h q hq
  exact ⟨N0, fun N hn => rat_bound_of_integer_precision hq (hN N hn) he⟩

end Collatz.NaturalDensity
