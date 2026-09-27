import CollatzTargetDensity.ArithmeticSeeds
import CollatzTargetDensity.RawBridge

/-! Seed selection with a multiplicative bound uniform in the target. -/
namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity
open scoped BigOperators
noncomputable section

theorem exists_odd_child_small {target : ℕ} (hodd : Odd target)
    (hthree : target % 3 ≠ 0) :
    ∃ c : ℕ, Odd c ∧ Tao.syracuse c = target ∧ c ≤ 2 * target := by
  have hnotdvd : ¬2 ∣ target := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  by_cases h : target % 3 = 1
  · let c := (4 * target - 1) / 3
    have he : 3 * c + 1 = 4 * target := by dsimp [c]; omega
    refine ⟨c, ⟨c / 2, by omega⟩, ?_, by omega⟩
    rw [Tao.syracuse_eq_ordCompl_two, he]
    exact Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two hnotdvd
  · let c := (2 * target - 1) / 3
    have he : 3 * c + 1 = 2 * target := by dsimp [c]; omega
    refine ⟨c, ⟨c / 2, by omega⟩, ?_, by omega⟩
    rw [Tao.syracuse_eq_ordCompl_two, he]
    exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two hnotdvd

/-- One finite bound covers two distinct one-step predecessors of one in
every residue class. The modulus and lower cutoff are fixed first. -/
theorem bounded_one_children (q X : ℕ) :
    ∃ D : ℕ, ∀ r : Fin (3 ^ q), ∃ x y : ℕ,
      X < x ∧ x < y ∧ y ≤ D ∧ Tao.syracuse x = 1 ∧
        Tao.syracuse y = 1 ∧ x % 3 ^ q = r ∧ y % 3 ^ q = r := by
  classical
  have hex (r : Fin (3 ^ q)) : ∃ x y : ℕ,
      X < x ∧ x < y ∧ Tao.syracuse x = 1 ∧ Tao.syracuse y = 1 ∧
        x % 3 ^ q = r ∧ y % 3 ^ q = r := by
    obtain ⟨x, hx, _, hhitx, hresx⟩ :=
      ResidueSeedCore.exists_large_oneStepSuccessful_root_in_residue q X r
    obtain ⟨y, hy, _, hhity, hresy⟩ :=
      ResidueSeedCore.exists_large_oneStepSuccessful_root_in_residue q x r
    exact ⟨x, y, hx, hy, hhitx, hhity, hresx, hresy⟩
  choose x y hx hxy hhitx hhity hresx hresy using hex
  refine ⟨∑ r, y r, ?_⟩
  intro r
  exact ⟨x r, y r, hx r, hxy r,
    Finset.single_le_sum (fun s _ => Nat.zero_le (y s)) (Finset.mem_univ r),
    hhitx r, hhity r, hresx r, hresy r⟩

def transportChild (c x : ℕ) : ℕ := (3 * c + 1) * x + c

theorem transportChild_odd {c : ℕ} (hc : Odd c) (x : ℕ) :
    Odd (transportChild c x) := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨(3 * k + 2) * x + k, ?_⟩
  simp only [transportChild, hk]
  ring

theorem transportChild_syracuse {c x : ℕ} (hx : Tao.syracuse x = 1) :
    Tao.syracuse (transportChild c x) = Tao.syracuse c := by
  have he : 3 * transportChild c x + 1 = (3 * c + 1) * (3 * x + 1) := by
    unfold transportChild
    ring
  rw [Tao.syracuse_eq_ordCompl_two, he, Nat.ordCompl_mul,
    ← Tao.syracuse_eq_ordCompl_two, ← Tao.syracuse_eq_ordCompl_two, hx, mul_one]

/-- The constant is independent of the positive target and of the requested
residue. No convergence assumption is used to select the nonperiodic child. -/
theorem bounded_seed_supply (q X : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ target : ℕ, Odd target → target % 3 ≠ 0 →
      ∀ r : Fin (3 ^ q), ∃ M : ℕ,
        Odd M ∧ X < M ∧ M ≤ C * target ∧ Tao.syracuse M = target ∧
          M % 3 ^ q = r ∧ Nonperiodic Tao.syracuse M := by
  obtain ⟨D, hD⟩ := bounded_one_children q X
  refine ⟨7 * D + 2, by omega, ?_⟩
  intro target hodd hthree r
  have ht : 1 ≤ target := by have := hodd.pos; omega
  obtain ⟨c, hc, hct, hsmall⟩ := exists_odd_child_small hodd hthree
  have hcop : Nat.Coprime (3 * c + 1) 3 := by
    simp [Nat.coprime_mul_left_add_left]
  have hunit : IsUnit ((3 * c + 1 : ℕ) : ZMod (3 ^ q)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right q)
  let f : ZMod (3 ^ q) → ZMod (3 ^ q) :=
    fun x => ((3 * c + 1 : ℕ) : ZMod (3 ^ q)) * x + c
  have hinj : Function.Injective f := by
    intro x y hxy
    exact hunit.mul_left_cancel (add_right_cancel hxy)
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective hinj (r.val : ZMod (3 ^ q))
  obtain ⟨x, y, hx, hxy, hyD, hhitx, hhity, hresx, hresy⟩ :=
    hD ⟨z.val, z.val_lt⟩
  have hproperties (w : ℕ) (hw : X < w) (hwD : w ≤ D)
      (hhit : Tao.syracuse w = 1) (hres : w % 3 ^ q = z.val) :
      Odd (transportChild c w) ∧ X < transportChild c w ∧
        transportChild c w ≤ (7 * D + 2) * target ∧
        Tao.syracuse (transportChild c w) = target ∧
        transportChild c w % 3 ^ q = r := by
    have hwcast : (w : ZMod (3 ^ q)) = z := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using hres
    have hcast : (transportChild c w : ZMod (3 ^ q)) = (r.val : ZMod (3 ^ q)) := by
      simpa only [transportChild, f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        hwcast] using hz
    refine ⟨transportChild_odd hc w, ?_, ?_, (transportChild_syracuse hhit).trans hct, ?_⟩
    · unfold transportChild
      nlinarith
    · calc
        transportChild c w ≤ (3 * c + 1) * D + c := by
          unfold transportChild
          gcongr
        _ ≤ (7 * D + 2) * target := by nlinarith
    · have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt r.isLt] using hv
  have hpx := hproperties x hx (hxy.le.trans hyD) hhitx hresx
  have hpy := hproperties y (hx.trans hxy) hyD hhity hresy
  have hne : transportChild c x ≠ transportChild c y := by
    unfold transportChild
    nlinarith
  rcases nonperiodic_choice hne (hpx.2.2.2.1.trans hpy.2.2.2.1.symm) with hnp | hnp
  · exact ⟨transportChild c x, hpx.1, hpx.2.1, hpx.2.2.1,
      hpx.2.2.2.1, hpx.2.2.2.2, hnp⟩
  · exact ⟨transportChild c y, hpy.1, hpy.2.1, hpy.2.2.1,
      hpy.2.2.2.1, hpy.2.2.2.2, hnp⟩

/-- Even targets admit an odd fertile predecessor with the same linear
size control. The factor nine is a convenient uniform bound. -/
theorem exists_fertile_raw_child_small {target : ℕ} (hthree : target % 3 ≠ 0) :
    ∃ c : ℕ, Odd c ∧ c % 3 ≠ 0 ∧ Reaches c target ∧ c ≤ 9 * target := by
  have ht : 1 ≤ target := by omega
  have hbase : ∃ c v : ℕ, Odd c ∧ 3 * c + 1 = 2 ^ v * target ∧ c ≤ 2 * target := by
    by_cases h : target % 3 = 1
    · let c := (4 * target - 1) / 3
      have he : 3 * c + 1 = 4 * target := by dsimp [c]; omega
      exact ⟨c, 2, ⟨c / 2, by omega⟩, he, by omega⟩
    · let c := (2 * target - 1) / 3
      have he : 3 * c + 1 = 2 * target := by dsimp [c]; omega
      exact ⟨c, 1, ⟨c / 2, by omega⟩, he, by omega⟩
  have hfertile : ∃ c v : ℕ, Odd c ∧ c % 3 ≠ 0 ∧
      3 * c + 1 = 2 ^ v * target ∧ c ≤ 9 * target := by
    obtain ⟨c, v, hc, he, hsmall⟩ := hbase
    by_cases h : c % 3 ≠ 0
    · exact ⟨c, v, hc, h, he, by omega⟩
    · refine ⟨4 * c + 1, v + 2, ⟨2 * c, by omega⟩, by omega, ?_, by omega⟩
      calc
        _ = 4 * (3 * c + 1) := by ring
        _ = 4 * (2 ^ v * target) := by rw [he]
        _ = _ := by rw [pow_add]; ring
  obtain ⟨c, v, hc, hunit, he, hsmall⟩ := hfertile
  refine ⟨c, hc, hunit, ⟨v + 1, ?_⟩, hsmall⟩
  rw [Function.iterate_add_apply, Function.iterate_one,
    collatzStep_eq_three_mul_add_one_of_odd hc, he]
  exact Tao.collatz_iterate_powTwo_mul v target

end
end CollatzTargetDensity
