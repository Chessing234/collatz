import Collatz.Strategy.BoundaryMoments
namespace Collatz.BoundaryCuts
variable {α : Type} [DecidableEq α]
def outside (L K : List α) := L.filter (fun z => decide (z ∉ K))
def inside (L K : List α) := L.filter (fun z => decide (z ∈ K))
theorem split (L K : List α) : (inside L K ++ outside L K).Perm L := by
  simpa [inside, outside] using List.filter_append_perm (fun z => decide (z ∈ K)) L

theorem common {L K : List α} (hL : L.Nodup) (hK : K.Nodup) :
    (inside L K).Perm (inside K L) := by
  apply (List.perm_ext_iff_of_nodup (hL.filter _) (hK.filter _)).mpr
  intro z
  simp [and_comm]

theorem balance {L K : List α} (hL : L.Nodup) (hK : K.Nodup)
    (hlen : L.length = K.length) : (outside L K).length = (outside K L).length := by
  have h1 := (split L K).length_eq
  have h2 := (split K L).length_eq
  have h3 := (common hL hK).length_eq
  simp only [List.length_append] at h1 h2
  omega

theorem zero_perm {L K : List α} (hL : L.Nodup) (hK : K.Nodup)
    (hlen : L.length = K.length) (h : (outside L K).length = 0) : L.Perm K := by
  have h' := balance hL hK hlen
  have hz : outside L K = [] := List.eq_nil_of_length_eq_zero h
  have hz' : outside K L = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hl := split L K
  have hk := split K L
  rw [hz, List.append_nil] at hl
  rw [hz', List.append_nil] at hk
  exact hl.symm.trans ((common hL hK).trans hk)

omit [DecidableEq α] in
theorem length_one {L : List α} (h : L.length=1) : ∃ x, L=[x] := by
  cases L with
  | nil => simp at h
  | cons x xs =>
    have hz : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using h)
    exact ⟨x, by rw [hz]⟩

theorem one_exchange {L K : List α} (hL : L.Nodup) (hK : K.Nodup)
    (hlen : L.length = K.length) (h : (outside L K).length = 1) :
    ∃ x y, (x :: K).Perm (y :: L) := by
  have h' := balance hL hK hlen
  obtain ⟨x,hx⟩ := length_one h
  obtain ⟨y,hy⟩ := length_one (show (outside K L).length=1 by omega)
  have hl := split L K
  have hk := split K L
  rw [hx] at hl
  rw [hy] at hk
  have hl' : L.Perm (x :: inside L K) := hl.symm.trans (List.perm_append_singleton _ _)
  have hk' : K.Perm (y :: inside K L) := hk.symm.trans (List.perm_append_singleton _ _)
  refine ⟨x,y,?_⟩
  exact (hk'.cons x).trans ((List.Perm.swap _ _ _).trans
    (((common hL hK).symm.cons x).cons y |>.trans (hl'.symm.cons y)))


/-- Boundary edges of one injective branch, counted without losing multiplicity. -/
def boundary (L : List α) (f : α → α) : Nat :=
  (outside L (L.map f)).length + (outside (L.map f) L).length

omit [DecidableEq α] in
theorem nodup_map {L : List α} (hL : L.Nodup) (f : α → α)
    (hi : ∀ a b, f a=f b → a=b) : (L.map f).Nodup :=
  hL.map f (fun a b hab he => hab (hi a b he))

theorem boundary_twice {L : List α} (hL : L.Nodup) (f : α → α)
    (hi : ∀ a b, f a=f b → a=b) :
    boundary L f = 2*(outside L (L.map f)).length := by
  have h := balance hL (nodup_map hL f hi) (by simp)
  unfold boundary
  omega

open Lean.Grind BoundaryMoments
attribute [local instance] Semiring.natCast
variable {R : Type} [CommRing R] [DecidableEq R]

/-- Algebraic form of the odd Collatz branch; u is the inverse of 2. -/
def oddBranch (u z : R) : R := u*(3*z+1)

/-- A genuine two-edge boundary yields one of the two moment obstructions.
This theorem derives the multiset exchange from the boundary count itself. -/
theorem two_boundary_obstruction (L : List R) (hL : L.Nodup) (u : R)
    (hu : 2*u=1) (h3 : ∀ a b : R, 3*a=3*b → a=b)
    (hb : boundary L (fun z => 2*z) + boundary L (oddBranch u)=2) :
    5*moment L 0*((moment L 0)^2-1)=0 ∨
    21*moment L 0*((moment L 0)^2-1)=0 := by
  have hi2 : ∀ a b : R, 2*a=2*b → a=b := by
    intro a b h
    have hh := congrArg (fun z => u*z) h
    grind
  have hiA : ∀ a b : R, oddBranch u a=oddBranch u b → a=b := by
    intro a b h
    apply h3 a b
    have hh := congrArg (fun z => 2*z) h
    simp only [oddBranch] at hh
    grind
  have hD := nodup_map hL (fun z => 2*z) hi2
  have hA := nodup_map hL (oddBranch u) hiA
  rw [boundary_twice hL _ hi2, boundary_twice hL _ hiA] at hb
  have hdich : (outside L (L.map (fun z => 2*z))).length=0 ∧
      (outside L (L.map (oddBranch u))).length=1 ∨
    (outside L (L.map (fun z => 2*z))).length=1 ∧
      (outside L (L.map (oddBranch u))).length=0 := by
    have hsplit : ∀ a b : Nat, 2*a+2*b=2 → a=0 ∧ b=1 ∨ a=1 ∧ b=0 := by
      intro a b hab; omega
    exact hsplit _ _ hb
  have hmap : (fun z : R => 2*oddBranch u z) = (fun z => 3*z+1) := by
    funext z; simp only [oddBranch]; grind
  rcases hdich with hdich | hdich
  · have hd := (zero_perm hL hD (by simp) hdich.1).symm
    obtain ⟨x,y,ha⟩ := one_exchange hL hA (by simp) hdich.2
    have ha' := ha.map (fun z => 2*z)
    simp only [List.map_cons, List.map_map, Function.comp_def, hmap] at ha'
    exact Or.inr (doubling_exchange_obstruction L x y hd ha')
  · have ha := (zero_perm hL hA (by simp) hdich.2).symm
    obtain ⟨x,y,hd⟩ := one_exchange hL hD (by simp) hdich.1
    have ha' := ha.map (fun z => 2*z)
    simp only [List.map_map, Function.comp_def, hmap] at ha'
    exact Or.inl (affine_exchange_obstruction L x y ha' hd)

/-- Uniform modular cardinality obstruction, valid also with zero divisors. -/
theorem two_boundary_annihilator (L : List R) (hL : L.Nodup) (u : R)
    (hu : 2*u=1) (h3 : ∀ a b : R, 3*a=3*b → a=b)
    (hb : boundary L (fun z => 2*z) + boundary L (oddBranch u)=2) :
    105*(Nat.cast L.length : R)*((Nat.cast L.length : R)^2-1)=0 := by
  have h := two_boundary_obstruction L hL u hu h3 hb
  simp only [moment_zero] at h
  clear hL hu h3 hb
  rcases h with h|h
  · calc
      _ = 21*(5*(Nat.cast L.length : R)*((Nat.cast L.length : R)^2-1)) := by grind
      _ = 0 := by rw [h]; grind
  · calc
      _ = 5*(21*(Nat.cast L.length : R)*((Nat.cast L.length : R)^2-1)) := by grind
      _ = 0 := by rw [h]; grind

end Collatz.BoundaryCuts
