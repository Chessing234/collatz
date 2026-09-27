import CollatzTargetDensity.SeedSupply
import CollatzTargetDensity.ResidueSeedCore

/-!+# Arbitrary-target nonperiodic seed supply

The residue coverage is the classical backward-mixing phenomenon. The proof
below uses the imported successful-root coverage as an arithmetic parameter
space, then transports it to another target by an affine map. It does not
assert that the new target converges to 1.
-/

namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity
noncomputable section

theorem exists_odd_child {target : ℕ} (hodd : Odd target) (hthree : target % 3 ≠ 0) :
    ∃ c : ℕ, Odd c ∧ Tao.syracuse c = target := by
  have hnotdvd : ¬2 ∣ target := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  by_cases h : target % 3 = 1
  · let c := (4 * target - 1) / 3
    have he : 3 * c + 1 = 4 * target := by dsimp [c]; omega
    refine ⟨c, ⟨c / 2, by omega⟩, ?_⟩
    rw [Tao.syracuse_eq_ordCompl_two, he]
    exact Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two hnotdvd
  · let c := (2 * target - 1) / 3
    have he : 3 * c + 1 = 2 * target := by dsimp [c]; omega
    refine ⟨c, ⟨c / 2, by omega⟩, ?_⟩
    rw [Tao.syracuse_eq_ordCompl_two, he]
    exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two hnotdvd

/-- The affine transform x ↦ (3c+1)x+c takes one-step predecessors of 1
    to one-step predecessors of S(c), and permutes every ternary residue space. -/
theorem large_child_in_residue {target c : ℕ} (hc : Odd c)
    (hct : Tao.syracuse c = target) (q X : ℕ) (r : Fin (3 ^ q)) :
    ∃ M : ℕ, Odd M ∧ X < M ∧ Tao.syracuse M = target ∧ M % 3 ^ q = r := by
  have hcop : Nat.Coprime (3 * c + 1) 3 := by
    rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
    norm_num
  have hunit : IsUnit ((3 * c + 1 : ℕ) : ZMod (3 ^ q)) := by
    apply (ZMod.isUnit_iff_coprime _ _).2
    simpa using hcop.pow 1 q
  let f : ZMod (3 ^ q) → ZMod (3 ^ q) :=
    fun x => ((3 * c + 1 : ℕ) : ZMod (3 ^ q)) * x + c
  have hinj : Function.Injective f := by
    intro x y hxy
    exact hunit.mul_left_cancel (add_right_cancel hxy)
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj (r.val : ZMod (3 ^ q))
  obtain ⟨x, hx, _hxodd, hxhit, hxres⟩ := ResidueSeedCore.exists_large_oneStepSuccessful_root_in_residue
    q X ⟨y.val, ZMod.val_lt y⟩
  let M := (3 * c + 1) * x + c
  have hxcast : (x : ZMod (3 ^ q)) = y := by
    calc
      _ = ((x % 3 ^ q : ℕ) : ZMod (3 ^ q)) := by simp
      _ = ((y.val : ℕ) : ZMod (3 ^ q)) := congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) hxres
      _ = y := ZMod.natCast_zmod_val y
  have hMcast : (M : ZMod (3 ^ q)) = (r.val : ZMod (3 ^ q)) := by
    simpa only [M, f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hxcast] using hy
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hc
    refine ⟨(3 * k + 2) * x + k, ?_⟩
    dsimp [M]
    rw [hk]
    ring
  · dsimp [M]
    nlinarith
  · have he : 3 * M + 1 = (3 * c + 1) * (3 * x + 1) := by dsimp [M]; ring
    rw [Tao.syracuse_eq_ordCompl_two, he, Nat.ordCompl_mul,
      ← Tao.syracuse_eq_ordCompl_two, ← Tao.syracuse_eq_ordCompl_two,
      hct, hxhit, mul_one]
  · have hv := congrArg ZMod.val hMcast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt r.isLt] using hv

/-- No unproved dynamical assumption: two distinct children in the same
    residue class allow exclusion of the unique possible periodic child. -/
theorem seed_supply {target : ℕ} (hodd : Odd target) (hthree : target % 3 ≠ 0) :
    SeedSupply target := by
  obtain ⟨c, hc, hct⟩ := exists_odd_child hodd hthree
  intro q X r
  obtain ⟨x, hxodd, hxlarge, hxhit, hxres⟩ := large_child_in_residue hc hct q X r
  obtain ⟨y, hyodd, hylarge, hyhit, hyres⟩ := large_child_in_residue hc hct q x r
  rcases nonperiodic_choice (Nat.ne_of_lt hylarge) (hxhit.trans hyhit.symm) with hx | hy
  · exact ⟨x, hxodd, hxlarge, hxhit, hxres, hx⟩
  · exact ⟨y, hyodd, hxlarge.trans hylarge, hyhit, hyres, hy⟩

end
end CollatzTargetDensity
