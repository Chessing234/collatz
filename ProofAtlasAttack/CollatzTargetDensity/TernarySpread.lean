import CollatzTargetDensity.ArithmeticSeeds
import CollatzTargetDensity.CountTransport

/-!
# Quantitative spreading into every ternary residue class

The classical sibling map `n ↦ 4*n+1` preserves the next Syracuse value
of an odd input. Its first `3^q` iterates cover every class modulo `3^q`.
Keeping the iterate index as a label controls collisions and transports
positive lower density. No equidistribution assertion is used.
-/
namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity
noncomputable section

def sibling (t n : ℕ) : ℕ :=
  4 ^ t * n + ndA5PreviousPhysicalCollapseSource t

theorem sibling_affine (t n : ℕ) :
    sibling t n = (3 * n + 1) * ndA5PreviousPhysicalCollapseSource t + n := by
  have h := three_mul_ndA5PreviousPhysicalCollapseSource_add_one t
  unfold sibling
  nlinarith

theorem sibling_odd (t : ℕ) {n : ℕ} (hn : Odd n) : Odd (sibling t n) := by
  cases t with
  | zero => simpa [sibling] using hn
  | succ t =>
    refine ⟨2 * (4 ^ t * n + ndA5PreviousPhysicalCollapseSource t), ?_⟩
    simp only [sibling, pow_succ, ndA5PreviousPhysicalCollapseSource_succ]
    ring

theorem sibling_syracuse (t n : ℕ) : Tao.syracuse (sibling t n) = Tao.syracuse n := by
  have he : 3 * sibling t n + 1 = 2 ^ (2 * t) * (3 * n + 1) := by
    have h := three_mul_ndA5PreviousPhysicalCollapseSource_add_one t
    have hp : 2 ^ (2 * t) = (4 : ℕ) ^ t := by rw [pow_mul]; norm_num
    rw [hp]
    unfold sibling
    nlinarith
  rw [Tao.syracuse_eq_ordCompl_two, he,
    Nat.ordCompl_self_pow_mul _ _ Nat.prime_two, ← Tao.syracuse_eq_ordCompl_two]

theorem sibling_injective (t : ℕ) : Function.Injective (sibling t) := by
  intro n m h
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4 ^ t) (Nat.add_right_cancel h)

theorem sibling_lt {t Q n X : ℕ} (ht : t < Q) (hn : n < X) :
    sibling t n < 4 ^ Q * X := by
  have hg := three_mul_ndA5PreviousPhysicalCollapseSource_add_one t
  have hsmall : sibling t n < 4 ^ t * (n + 1) := by unfold sibling; nlinarith
  have hp : (4 : ℕ) ^ t ≤ 4 ^ Q := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ht)
  exact hsmall.trans_le (Nat.mul_le_mul hp (by omega))

/-- Every input, without a convergence hypothesis, has a sibling in every
ternary residue within the first full period. -/
theorem sibling_residue (q n : ℕ) (r : Fin (3 ^ q)) :
    ∃ t : ℕ, t < 3 ^ q ∧ sibling t n % 3 ^ q = r := by
  have hcop : Nat.Coprime (3 * n + 1) 3 := by
    rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
    norm_num
  have hunit : IsUnit ((3 * n + 1 : ℕ) : ZMod (3 ^ q)) := by
    apply (ZMod.isUnit_iff_coprime _ _).2
    simpa using hcop.pow 1 q
  let f : ZMod (3 ^ q) → ZMod (3 ^ q) :=
    fun x => ((3 * n + 1 : ℕ) : ZMod (3 ^ q)) * x + n
  have hinj : Function.Injective f := by
    intro x y hxy
    exact hunit.mul_left_cancel (add_right_cancel hxy)
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj (r.val : ZMod (3 ^ q))
  obtain ⟨t, ht⟩ := ResidueSeedCore.ndCollapseSource_residue_surjective q
    ⟨y.val, ZMod.val_lt y⟩
  have htmod : ndA5PreviousPhysicalCollapseSource t % 3 ^ q = y.val :=
    congrArg Fin.val ht
  have htcast : (ndA5PreviousPhysicalCollapseSource t : ZMod (3 ^ q)) = y := by
    calc
      _ = ((ndA5PreviousPhysicalCollapseSource t % 3 ^ q : ℕ) : ZMod (3 ^ q)) := by simp
      _ = ((y.val : ℕ) : ZMod (3 ^ q)) := congrArg (fun a : ℕ => (a : ZMod (3 ^ q))) htmod
      _ = y := ZMod.natCast_zmod_val y
  have he : (sibling t n : ZMod (3 ^ q)) = (r.val : ZMod (3 ^ q)) := by
    rw [sibling_affine]
    simpa only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, htcast] using hy
  refine ⟨t, t.isLt, ?_⟩
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt r.isLt] using hv

def inTernaryClass (B : Set ℕ) (q : ℕ) (r : Fin (3 ^ q)) : Set ℕ :=
  {n | n ∈ B ∧ n % 3 ^ q = r}

/-- A finite, explicit comparison valid at every cutoff and every modulus. -/
theorem ternary_count_transport (A B : Set ℕ)
    (hclosed : ∀ t n, n ∈ A → sibling t n ∈ B)
    (q : ℕ) (r : Fin (3 ^ q)) (X : ℕ) :
    Terras.natCount A X ≤ 3 ^ q *
      Terras.natCount (inTernaryClass B q r) (4 ^ (3 ^ q) * X) := by
  classical
  let label : ℕ → ℕ := fun n => Classical.choose (sibling_residue q n r)
  have hl (n : ℕ) : label n < 3 ^ q ∧ sibling (label n) n % 3 ^ q = r :=
    Classical.choose_spec (sibling_residue q n r)
  apply count_le_of_labelled_injection A (inTernaryClass B q r)
    (3 ^ q) (4 ^ (3 ^ q)) label (fun n => sibling (label n) n)
  · intro n m h
    have hlab := congrArg Prod.fst h
    have hout := congrArg Prod.snd h
    dsimp only at hlab hout
    rw [hlab] at hout
    exact sibling_injective (label m) hout
  · exact fun n => (hl n).1
  · exact fun n hn => ⟨hclosed (label n) n hn, (hl n).2⟩
  · exact fun n Y hn => sibling_lt (hl n).1 hn

theorem positive_density_in_ternary_class {A B : Set ℕ}
    (hclosed : ∀ t n, n ∈ A → sibling t n ∈ B)
    (hA : HasPositiveLowerDensity A) (q : ℕ) (r : Fin (3 ^ q)) :
    HasPositiveLowerDensity (inTernaryClass B q r) :=
  positive_density_of_count_transport (by positivity) (by positivity)
    (ternary_count_transport A B hclosed q r) hA

end
end CollatzTargetDensity
