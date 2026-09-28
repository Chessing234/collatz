import Collatz.Strategy.PeriodicTwoDefectOdd
import Collatz.Strategy.PeriodicSingleDefectAll

/-!
Two-defect classification for every positive modulus divisible by three.
The new ingredient is a descent dichotomy for labels on the directed line graph.
This is a finite structural theorem, not a convergence theorem.
-/

namespace Collatz.PeriodicTwoDefectAll
variable {α : Type}
open PeriodicRigidity PeriodicDefectMinimum PeriodicSingleDefectAll

/-- Exactly two residue classes of defective inputs. -/
def ExactlyTwo (m : Nat) (f : Nat → α) : Prop :=
  ∃ r s, r < 2*m ∧ s < 2*m ∧ r ≠ s ∧
    ∀ n, Defect f n ↔ n%(2*m)=r ∨ n%(2*m)=s

/-- An edge is encoded by its input residue modulo twice the lower modulus. -/
def PairBound (M : Nat) (f : Nat → α) (r s : Nat) : Prop :=
  ∀ a b, a < 2*M → b < 2*M → acceleratedStep a % M = b % M →
    f a ≠ f b →
    (a = r%(2*M) ∧ b = acceleratedStep r%(2*M)) ∨
    (a = s%(2*M) ∧ b = acceleratedStep s%(2*M))

theorem pair_bound {f : Nat → α} {M r s : Nat} (hM : 0 < M)
    (hp : HasPeriod f (2*M))
    (hex : ∀ n, Defect f n ↔ n%(4*M)=r ∨ n%(4*M)=s) :
    PairBound M f r s := by
  intro a b ha hb he hne
  obtain ⟨u,hu,hua,hub⟩ := composable_lift hM ha hb he
  have hd : Defect f u := by
    unfold Defect
    rw [period_mod hp (acceleratedStep u),period_mod hp u,hua,hub]
    exact Ne.symm hne
  have hh := (hex u).mp hd
  rw [Nat.mod_eq_of_lt (by omega)] at hh
  rcases hh with h | h <;> subst u
  · exact Or.inl ⟨hua.symm,hub.symm⟩
  · exact Or.inr ⟨hua.symm,hub.symm⟩

theorem even_step (n : Nat) : acceleratedStep (2*n) = n := by
  simp [acceleratedStep]

/-- Away from the residue 2 modulo 3, the incoming edge is unique. -/
theorem unique_incoming {M a v : Nat} (_hM : 0 < M) (h3 : M%3=0)
    (ha : a < 2*M) (_hv : v < M) (ht : acceleratedStep a % M=v)
    (hv3 : v%3 ≠ 2) : a = 2*v := by
  by_cases he : a%2=0
  · have hs : acceleratedStep a=a/2 := by simp [acceleratedStep,he]
    rw [hs,Nat.mod_eq_of_lt (by omega)] at ht
    omega
  · have hs : acceleratedStep a%3=2 := by
      unfold acceleratedStep; rw [if_neg he]; omega
    have hd : 3 ∣ M := Nat.dvd_of_mod_eq_zero h3
    have hh := Nat.mod_mod_of_dvd (acceleratedStep a) hd
    rw [ht,hs] at hh
    exact False.elim (hv3 hh)

/-- A vertex with an odd predecessor has at least three distinct incoming edges. -/
theorem three_incoming {M v : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hv : v < M) (hv3 : v%3=2) :
    ∃ a b c, a < 2*M ∧ b < 2*M ∧ c < 2*M ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      acceleratedStep a%M=v ∧ acceleratedStep b%M=v ∧ acceleratedStep c%M=v := by
  let a := 2*(v/3)+1
  let b := a+2*(M/3)
  have ha : a%2=1 := by dsimp [a]; omega
  have hb : b%2=1 := by dsimp [b]; omega
  have hsa : acceleratedStep a=v := by
    unfold acceleratedStep; rw [if_neg (by omega : ¬a%2=0)]
    dsimp [a]; omega
  have hsb : acceleratedStep b=v+M := by
    dsimp [b]; rw [step_add_even,if_neg (by omega : ¬a%2=0),hsa]; omega
  refine ⟨2*v,a,b,by omega,?_,?_,by omega,by omega,?_,?_,?_,?_⟩
  · dsimp [a]; omega
  · dsimp [b,a]; omega
  · dsimp [b]; omega
  · rw [even_step,Nat.mod_eq_of_lt hv]
  · rw [hsa,Nat.mod_eq_of_lt hv]
  · rw [hsb,Nat.add_mod_right,Nat.mod_eq_of_lt hv]

/-- If the two outgoing edge labels differ, every incoming edge is one of two. -/
theorem split_outgoing_incoming_bound {f : Nat → α} {M r s v a : Nat}
    (_hM : 0 < M) (hb : PairBound M f r s) (hv : v < M)
    (hsplit : f v ≠ f (v+M)) (ha : a < 2*M)
    (ht : acceleratedStep a%M=v) : a=r%(2*M) ∨ a=s%(2*M) := by
  by_cases h : f a=f v
  · have hn : f a ≠ f (v+M) := fun he => hsplit (h.symm.trans he)
    have hh := hb a (v+M) ha (by omega)
      (by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hv]; exact ht) hn
    exact hh.imp And.left And.left
  · have hh := hb a v ha (by omega) (by rw [Nat.mod_eq_of_lt hv]; exact ht) h
    exact hh.imp And.left And.left

/-- No outgoing split is possible at a vertex of indegree four. -/
theorem high_indegree_no_split {f : Nat → α} {M r s v : Nat}
    (hM : 0 < M) (h3 : M%3=0) (hb : PairBound M f r s)
    (hv : v < M) (hv3 : v%3=2) : f v=f (v+M) := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨a,b,c,ha,hb',hc,hab,hac,hbc,hat,hbt,hct⟩ := three_incoming hM h3 hv hv3
  have h1 := split_outgoing_incoming_bound hM hb hv hn ha hat
  have h2 := split_outgoing_incoming_bound hM hb hv hn hb' hbt
  have h3 := split_outgoing_incoming_bound hM hb hv hn hc hct
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> rcases h3 with h3|h3 <;> omega

/-- A nonuniform incoming fibre consumes the whole two-transition budget. -/
theorem incoming_split_forces_period {f : Nat → α} {M r s a b : Nat}
    (hM : 0 < M) (h3 : M%3=0) (hp : HasPeriod f (2*M))
    (hb : PairBound M f r s) (ha : a < 2*M) (hb' : b < 2*M)
    (ht : acceleratedStep a%M=acceleratedStep b%M) (hne : f a ≠ f b) :
    HasPeriod f M := by
  let v := acceleratedStep a%M
  have hv : v < M := Nat.mod_lt _ hM
  have hv3 : v%3=2 := by
    by_cases hh : v%3=2
    · exact hh
    · have h1 := unique_incoming hM h3 ha hv rfl hh
      have h2 := unique_incoming hM h3 hb' hv ht.symm hh
      exact False.elim (hne (congrArg f (h1.trans h2.symm)))
  have hsplit : ∀ w, w < M → f w=f (w+M) := by
    intro w hw
    by_cases hwv : w=v
    · subst w; exact high_indegree_no_split hM h3 hb hv hv3
    · apply Classical.byContradiction
      intro hdiff
      have pick : ∀ c, c < 2*M → c%M=v →
          acceleratedStep r%(2*M)=c ∨ acceleratedStep s%(2*M)=c := by
        intro c hc hcv
        by_cases hh : f a=f c
        · have hn : f b ≠ f c := fun he => hne (hh.trans he.symm)
          have hz := hb b c hb' hc (ht.symm.trans hcv.symm) hn
          exact hz.imp (fun h => h.2.symm) (fun h => h.2.symm)
        · have hz := hb a c ha hc hcv.symm hh
          exact hz.imp (fun h => h.2.symm) (fun h => h.2.symm)
      have p0 := pick v (by omega) (Nat.mod_eq_of_lt hv)
      have p1 := pick (v+M) (by omega) (by simp [Nat.mod_eq_of_lt hv])
      have bound := split_outgoing_incoming_bound hM hb hw hdiff
        (show 2*w < 2*M by omega) (by rw [even_step,Nat.mod_eq_of_lt hw])
      have unequal : f (2*w) ≠ f w ∨ f (2*w) ≠ f (w+M) := by
        by_cases h : f (2*w)=f w
        · exact Or.inr (fun he => hdiff (h.symm.trans he))
        · exact Or.inl h
      have p2 : acceleratedStep r%(2*M)%M=w ∨ acceleratedStep s%(2*M)%M=w := by
        rcases unequal with hh|hh
        · have hh' := hb (2*w) w (by omega) (by omega)
            (by rw [even_step]) hh
          rcases hh' with hh'|hh'
          · exact Or.inl (by rw [← hh'.2,Nat.mod_eq_of_lt hw])
          · exact Or.inr (by rw [← hh'.2,Nat.mod_eq_of_lt hw])
        · have hh' := hb (2*w) (w+M) (by omega) (by omega)
            (by rw [even_step,Nat.add_mod_right]) hh
          rcases hh' with hh'|hh'
          · exact Or.inl (by rw [← hh'.2,Nat.add_mod_right,Nat.mod_eq_of_lt hw])
          · exact Or.inr (by rw [← hh'.2,Nat.add_mod_right,Nat.mod_eq_of_lt hw])
      rcases p0 with p0|p0 <;> rcases p1 with p1|p1 <;> rcases p2 with p2|p2 <;>
        simp_all [Nat.mod_eq_of_lt hv]
  intro n
  have hh := hsplit (n%M) (Nat.mod_lt _ hM)
  have hn : n%(2*M) < 2*M := Nat.mod_lt _ (by omega)
  have hmod : n%(2*M)%M=n%M := Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left M 2)
  rcases two_lifts hM hn (show n%M < 2*M by have := Nat.mod_lt n hM; omega) (by rw [Nat.mod_mod]; exact hmod) with h|h
  · rw [period_mod hp (n+M),period_mod hp n,Nat.add_mod,h]
    simp only [Nat.mod_eq_of_lt (by omega : M < 2*M),Nat.mod_eq_of_lt (by have := Nat.mod_lt n hM; omega : n%M+M < 2*M)]
    exact hh.symm
  · rw [period_mod hp (n+M),period_mod hp n,Nat.add_mod,
      Nat.mod_eq_of_lt (by omega : M < 2*M),h]
    have hn' : n%(2*M)=n%M+M := by
      by_cases hlt : n%(2*M)+M < 2*M
      · rw [Nat.mod_eq_of_lt hlt] at h; have := Nat.mod_lt n hM; omega
      · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at h; omega
    rw [hn']; exact hh

/-- A genuine smaller period duplicates each defect, so two become one. -/
theorem half_period_one {f : Nat → α} {M : Nat} (hM : 0 < M)
    (hp : HasPeriod f M) (he : ExactlyTwo (2*M) f) :
    ∃ d, d < 2*M ∧ ∀ n, Defect f n ↔ n%(2*M)=d := by
  obtain ⟨r,s,hr,hs,hrs,hex⟩ := he
  have hex' : ∀ n, Defect f n ↔ n%(4*M)=r ∨ n%(4*M)=s := by
    simpa [show 2*(2*M)=4*M by omega] using hex
  let d := r%(2*M)
  have hd : d < 2*M := Nat.mod_lt _ (by omega)
  have hdr : Defect f r := (hex r).mpr (Or.inl (Nat.mod_eq_of_lt hr))
  have hd0 : Defect f d := by rw [← period_mod (defect_period hp) r]; exact hdr
  have hd1 : Defect f (d+2*M) := by rw [defect_period hp]; exact hd0
  have p0 := (hex' d).mp hd0
  have p1 := (hex' (d+2*M)).mp hd1
  rw [Nat.mod_eq_of_lt (by omega)] at p0 p1
  have hsd : s%(2*M)=d := by
    rcases p0 with p0|p0 <;> rcases p1 with p1|p1
    · omega
    · rw [← p1,Nat.add_mod_right,Nat.mod_eq_of_lt hd]
    · rw [← p0,Nat.mod_eq_of_lt hd]
    · omega
  refine ⟨d,hd,?_⟩
  intro n
  constructor
  · intro hn
    have hh := (hex n).mp hn
    have hmod := Nat.mod_mod_of_dvd n (Nat.dvd_mul_left (2*M) 2)
    rcases hh with hh|hh
    · rw [hh] at hmod; exact hmod.symm
    · rw [hh,hsd] at hmod; exact hmod.symm
  · intro hn
    rw [period_mod (defect_period hp) n,hn]
    exact hd0

/-- When incoming labels agree, they define a lower label pulled back by T. -/
theorem incoming_uniform_pullback {f : Nat → α} {M : Nat} (hM : 0 < M)
    (hp : HasPeriod f (2*M))
    (hi : ∀ a b, a < 2*M → b < 2*M →
      acceleratedStep a%M=acceleratedStep b%M → f a=f b) :
    let g := fun n => f (2*(n%M))
    HasPeriod g M ∧ ∀ n, f n=g (acceleratedStep n) := by
  let g := fun n => f (2*(n%M))
  refine ⟨by intro n; simp,?_⟩
  intro n
  have hn : n%(2*M) < 2*M := Nat.mod_lt _ (by omega)
  have hv : acceleratedStep n%M < M := Nat.mod_lt _ hM
  have ht : acceleratedStep (n%(2*M))%M=acceleratedStep n%M :=
    (period_mod (output_period M) n).symm
  rw [period_mod hp n]
  apply hi _ _ hn (by omega)
  rw [even_step,Nat.mod_mod]
  exact ht

/-- Pulling a two-defect label down through T preserves precisely two defects.
The alternative one-defect case is excluded by uniqueness of the edge entering M. -/
theorem pullback_two {f g : Nat → α} {M : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hgp : HasPeriod g M) (hl : ∀ n, f n=g (acceleratedStep n))
    (he : ExactlyTwo (2*M) f) : ExactlyTwo M g := by
  obtain ⟨r,s,hr,hs,hrs,hex⟩ := he
  let b := acceleratedStep r%(2*M)
  let c := acceleratedStep s%(2*M)
  have hb : b < 2*M := Nat.mod_lt _ (by omega)
  have hc : c < 2*M := Nat.mod_lt _ (by omega)
  have hd : ∀ n, Defect f n ↔ Defect g (acceleratedStep n) := by
    intro n; unfold Defect; rw [hl (acceleratedStep n),hl n]
  have hdb : Defect g b := by
    rw [← period_mod (defect_period hgp) (acceleratedStep r)]
    exact (hd r).mp ((hex r).mpr (Or.inl (Nat.mod_eq_of_lt hr)))
  have hdc : Defect g c := by
    rw [← period_mod (defect_period hgp) (acceleratedStep s)]
    exact (hd s).mp ((hex s).mpr (Or.inr (Nat.mod_eq_of_lt hs)))
  have hgex : ∀ n, Defect g n ↔ n%(2*M)=b ∨ n%(2*M)=c := by
    intro n
    constructor
    · intro hn
      have hdf : Defect f (2*n) := by rw [hd,even_step]; exact hn
      have hh := (hex (2*n)).mp hdf
      have ht := period_mod (output_period (2*M)) (2*n)
      rw [even_step] at ht
      rcases hh with hh|hh
      · rw [hh] at ht; exact Or.inl ht
      · rw [hh] at ht; exact Or.inr ht
    · intro hn
      rw [period_mod (defect_period hgp) n]
      rcases hn with hn|hn
      · rw [hn]; exact hdb
      · rw [hn]; exact hdc
  have hbc : b ≠ c := by
    intro hbc
    have hone : ∀ n, Defect g n ↔ n%(2*M)=b := by
      intro n; rw [hgex,← hbc]; simp
    obtain ⟨hbm,_,_⟩ := all_single_defect M hM h3 g b hb hgp hone
    have hr' : acceleratedStep r%(2*M)=M := hbm
    have hs' : acceleratedStep s%(2*M)=M := hbc.symm.trans hbm
    have h23 : (2*M)%3=0 := by omega
    have hM3 : M%3 ≠ 2 := by omega
    have hrr := unique_incoming (by omega : 0 < 2*M) h23 hr (by omega) hr' hM3
    have hss := unique_incoming (by omega : 0 < 2*M) h23 hs (by omega) hs' hM3
    exact hrs (hrr.trans hss.symm)
  exact ⟨b,c,hb,hc,hbc,hgex⟩

/-- The even-modulus descent dichotomy. -/
theorem descent_dichotomy {f : Nat → α} {M : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hp : HasPeriod f (2*M)) (he : ExactlyTwo (2*M) f) :
    HasPeriod f M ∨ ∃ g, HasPeriod g M ∧ ExactlyTwo M g ∧
      ∀ n, f n=g (acceleratedStep n) := by
  classical
  by_cases hi : ∀ a b, a < 2*M → b < 2*M →
      acceleratedStep a%M=acceleratedStep b%M → f a=f b
  · obtain ⟨hgp,hl⟩ := incoming_uniform_pullback hM hp hi
    exact Or.inr ⟨_,hgp,pullback_two hM h3 hgp hl he,hl⟩
  · have hn : ∃ a b, a < 2*M ∧ b < 2*M ∧
        acceleratedStep a%M=acceleratedStep b%M ∧ f a ≠ f b := by
      apply Classical.byContradiction
      intro h
      apply hi
      intro a b ha hb ht
      apply Classical.byContradiction
      intro hne
      exact h ⟨a,b,ha,hb,ht,hne⟩
    obtain ⟨a,b,ha,hb,ht,hab⟩ := hn
    obtain ⟨r,s,_,_,_,hex⟩ := he
    have hex' : ∀ n, Defect f n ↔ n%(4*M)=r ∨ n%(4*M)=s := by
      simpa [show 2*(2*M)=4*M by omega] using hex
    exact Or.inl (incoming_split_forces_period hM h3 hp
      (pair_bound hM hp hex') ha hb ht hab)

/-- The two lifts of any fixed residue into the doubled modulus. -/
theorem residue_lifts {M d : Nat} (hM : 0 < M) (hd : d < M) (n : Nat) :
    n%M=d ↔ n%(2*M)=d ∨ n%(2*M)=d+M := by
  have hn : n%(2*M) < 2*M := Nat.mod_lt _ (by omega)
  have hm := Nat.mod_mod_of_dvd n (Nat.dvd_mul_left M 2)
  by_cases hl : n%(2*M) < M
  · rw [Nat.mod_eq_of_lt hl] at hm; omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at hm; omega

theorem half_residues {M : Nat} (hM : 0 < M) (n : Nat) :
    n%M=0 ↔ n%(2*M)=0 ∨ n%(2*M)=M := by
  simpa using residue_lifts hM hM n

/-- The full preimage of a vertex outside the odd-branch range is one edge. -/
theorem preimage_residue {M v : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hv : v < M) (hv3 : v%3 ≠ 2) (n : Nat) :
    acceleratedStep n%M=v ↔ n%(2*M)=2*v := by
  have ht := period_mod (output_period M) n
  constructor
  · intro hh
    exact unique_incoming hM h3 (Nat.mod_lt _ (by omega)) hv (ht.symm.trans hh) hv3
  · intro hh
    rw [ht,hh,even_step,Nat.mod_eq_of_lt hv]

/-- The exceptional residues are zero and half the modulus. -/
def HalfShape (m : Nat) (f : Nat → α) : Prop :=
  ∃ h A B, m=2*h ∧ A ≠ B ∧
    ∀ n, f n=if n%m=0 ∨ n%m=h then A else B

/-- The exceptional residues are one third and two thirds of the modulus. -/
def ThirdShape (m : Nat) (f : Nat → α) : Prop :=
  ∃ h A B, m=3*h ∧ h%3=0 ∧ A ≠ B ∧
    ∀ n, f n=if n%m=h ∨ n%m=2*h then A else B

/-- A smaller-period branch has exactly the half-modulus form. -/
theorem half_shape_of_period {f : Nat → α} {M : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hp : HasPeriod f M) (he : ExactlyTwo (2*M) f) : HalfShape (2*M) f := by
  obtain ⟨d,hd,hex⟩ := half_period_one hM hp he
  obtain ⟨_,hne,hc⟩ := all_single_defect M hM h3 f d hd hp hex
  refine ⟨M,f 0,f 1,rfl,hne,?_⟩
  intro n
  simp only [← half_residues hM]
  by_cases hn : n%M=0
  · rw [if_pos hn,period_mod hp n,hn]
  · rw [if_neg hn]; exact hc n hn

/-- The two classified shapes are stable under pullback by T. -/
theorem shapes_pullback {f g : Nat → α} {M : Nat} (hM : 0 < M) (h3 : M%3=0)
    (hl : ∀ n, f n=g (acceleratedStep n))
    (hs : HalfShape M g ∨ ThirdShape M g) :
    HalfShape (2*M) f ∨ ThirdShape (2*M) f := by
  rcases hs with ⟨h,A,B,hm,hne,hform⟩ | ⟨h,A,B,hm,hh3,hne,hform⟩
  · subst M
    have hh3 : h%3=0 := by omega
    left
    refine ⟨2*h,A,B,rfl,hne,?_⟩
    intro n
    rw [hl,hform]
    simp only [preimage_residue hM h3 (by omega : 0 < 2*h) (by decide),
      preimage_residue hM h3 (by omega : h < 2*h) (by omega)]
  · subst M
    right
    refine ⟨2*h,A,B,by omega,by omega,hne,?_⟩
    intro n
    rw [hl,hform]
    simp only [preimage_residue hM h3 (by omega : h < 3*h) (by omega),
      preimage_residue hM h3 (by omega : 2*h < 3*h) (by omega)]

/-- Exhaustive two-defect rigidity for all positive moduli divisible by three. -/
theorem two_defect_shapes (m : Nat) (hm : 0 < m) (h3 : m%3=0)
    (f : Nat → α) (hp : HasPeriod f m) (he : ExactlyTwo m f) :
    HalfShape m f ∨ ThirdShape m f := by
  induction m using Nat.strongRecOn generalizing f with
  | ind m ih =>
    by_cases heven : m%2=0
    · have hmEq : m=2*(m/2) := by omega
      obtain ⟨M,hmEq⟩ : ∃ M, m=2*M := ⟨m/2,hmEq⟩
      subst m
      have hM : 0 < M := by omega
      have hM3 : M%3=0 := by omega
      rcases descent_dichotomy hM hM3 hp he with hfp | ⟨g,hgp,hge,hl⟩
      · exact Or.inl (half_shape_of_period hM hM3 hfp he)
      · exact shapes_pullback hM hM3 hl (ih M (by omega) hM hM3 g hgp hge)
    · obtain ⟨h,hmEq⟩ := Nat.dvd_of_mod_eq_zero h3
      subst m
      have hodd : (3*h)%2=1 := by omega
      have hex : ∃ r s, r < 6*h ∧ s < 6*h ∧ r ≠ s ∧
          ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s := by
        simpa [ExactlyTwo,show 2*(3*h)=6*h by omega] using he
      obtain ⟨hh3,hne,hform⟩ := (PeriodicTwoDefectOdd.two_defect_classification
        (by omega : 0 < h) hodd hp).mp hex
      exact Or.inr ⟨h,f h,f 1,rfl,hh3,hne,hform⟩

/-- Relabelling a Boolean partition by distinct values preserves defects. -/
theorem two_label_defect {f : Nat → α} {p : Nat → Prop} [DecidablePred p]
    {A B : α} (hne : A ≠ B) (hf : ∀ n, f n=if p n then A else B) (n : Nat) :
    Defect f n ↔ (p (acceleratedStep n) ∧ ¬p n) ∨ (¬p (acceleratedStep n) ∧ p n) := by
  unfold Defect
  rw [hf (acceleratedStep n),hf n]
  by_cases ht : p (acceleratedStep n) <;> by_cases hn : p n <;>
    simp [ht,hn,hne,Ne.symm hne]

/-- The half-modulus family has errors at h and 3h modulo 4h. -/
theorem half_shape_positions {f : Nat → α} {h : Nat} {A B : α}
    (hh : 0 < h) (h3 : h%3=0) (hne : A ≠ B)
    (hf : ∀ n, f n=if n%(2*h)=0 ∨ n%(2*h)=h then A else B) :
    ∀ n, Defect f n ↔ n%(4*h)=h ∨ n%(4*h)=3*h := by
  have hf' : ∀ n, f n=if n%h=0 then A else B := by
    intro n; simpa only [half_residues hh] using hf n
  have hd : ∀ n, Defect f n ↔ Defect (divisibleLabel h) n := by
    intro n
    rw [two_label_defect hne hf']
    unfold Defect divisibleLabel
    by_cases ht : acceleratedStep n%h=0 <;> by_cases hn : n%h=0 <;> simp [ht,hn]
  intro n
  rw [hd,divisibleLabel_defect hh h3]
  simpa [show 2*(2*h)=4*h by omega,show h+2*h=3*h by omega] using
    residue_lifts (by omega : 0 < 2*h) (by omega : h < 2*h) n

/-- The third-modulus family has errors at h and 5h modulo 6h, for either parity. -/
theorem third_shape_positions {f : Nat → α} {h : Nat} {A B : α}
    (hh : 0 < h) (h3 : h%3=0) (hne : A ≠ B)
    (hf : ∀ n, f n=if n%(3*h)=h ∨ n%(3*h)=2*h then A else B) :
    ∀ n, Defect f n ↔ n%(6*h)=h ∨ n%(6*h)=5*h := by
  intro n
  rw [two_label_defect hne hf,
    preimage_residue (by omega : 0 < 3*h) (by omega) (by omega : h < 3*h) (by omega),
    preimage_residue (by omega : 0 < 3*h) (by omega) (by omega : 2*h < 3*h) (by omega),
    residue_lifts (by omega : 0 < 3*h) (by omega : h < 3*h),
    residue_lifts (by omega : 0 < 3*h) (by omega : 2*h < 3*h)]
  simp only [show 2*(3*h)=6*h by omega,show h+3*h=4*h by omega,
    show 2*h+3*h=5*h by omega,show 2*(2*h)=4*h by omega]
  omega

/-- Complete classification, including attainability, without a parity restriction. -/
theorem two_defect_classification {m : Nat} (hm : 0 < m) (h3 : m%3=0)
    {f : Nat → α} (hp : HasPeriod f m) :
    ExactlyTwo m f ↔ HalfShape m f ∨ ThirdShape m f := by
  constructor
  · exact two_defect_shapes m hm h3 f hp
  · intro hs
    rcases hs with ⟨h,A,B,hmEq,hne,hform⟩ | ⟨h,A,B,hmEq,hh3,hne,hform⟩
    · subst m
      refine ⟨h,3*h,by omega,by omega,by omega,?_⟩
      simpa [show 2*(2*h)=4*h by omega] using
        half_shape_positions (by omega : 0 < h) (by omega) hne hform
    · subst m
      refine ⟨h,5*h,by omega,by omega,by omega,?_⟩
      simpa [show 2*(3*h)=6*h by omega] using
        third_shape_positions (by omega : 0 < h) hh3 hne hform

/-- Exact existence criterion for Boolean two-defect labels. -/
theorem exists_two_iff {m : Nat} (hm : 0 < m) (h3 : m%3=0) :
    (∃ f : Nat → Bool, HasPeriod f m ∧ ExactlyTwo m f) ↔ m%6=0 ∨ m%9=0 := by
  constructor
  · rintro ⟨f,hp,he⟩
    rcases (two_defect_classification hm h3 hp).mp he with
      ⟨h,A,B,hmEq,_⟩ | ⟨h,A,B,hmEq,hh3,_⟩
    · left; omega
    · right; omega
  · intro hh
    rcases hh with hh|hh
    · let h := m/2
      have hmEq : m=2*h := by dsimp [h]; omega
      let f := fun n => if n%m=0 ∨ n%m=h then true else false
      have hp : HasPeriod f m := by intro n; simp [f]
      refine ⟨f,hp,(two_defect_classification hm h3 hp).mpr (Or.inl ?_)⟩
      exact ⟨h,true,false,hmEq,by decide,fun _ => rfl⟩
    · let h := m/3
      have hmEq : m=3*h := by dsimp [h]; omega
      have hh3 : h%3=0 := by dsimp [h]; omega
      let f := fun n => if n%m=h ∨ n%m=2*h then true else false
      have hp : HasPeriod f m := by intro n; simp [f]
      refine ⟨f,hp,(two_defect_classification hm h3 hp).mpr (Or.inr ?_)⟩
      exact ⟨h,true,false,hmEq,hh3,by decide,fun _ => rfl⟩

/-- The half-modulus shape always has a smaller period. -/
theorem half_shape_smaller_period {f : Nat → α} {m : Nat} (hm : 0 < m)
    (hs : HalfShape m f) : ∃ h, 0 < h ∧ h < m ∧ HasPeriod f h := by
  obtain ⟨h,A,B,hmEq,_,hf⟩ := hs
  subst m
  have hh : 0 < h := by omega
  refine ⟨h,hh,by omega,?_⟩
  intro n
  rw [hf (n+h),hf n]
  simp only [← half_residues hh,Nat.add_mod_right]

/-- A third-modulus shape has precisely the displayed least period. -/
theorem third_shape_least_period {f : Nat → α} {m : Nat} (hm : 0 < m)
    (hs : ThirdShape m f) : ∀ d, 0 < d → HasPeriod f d → m ≤ d := by
  obtain ⟨h,A,B,hmEq,_,hne,hf⟩ := hs
  subst m
  have hh : 0 < h := by omega
  have hfh : f h=A := by simp [hf h,Nat.mod_eq_of_lt (by omega : h < 3*h)]
  have hf2 : f (2*h)=A := by simp [hf (2*h),Nat.mod_eq_of_lt (by omega : 2*h < 3*h)]
  have hf0 : f (3*h)=B := by simp [hf (3*h),show 0 ≠ h by omega,show 0 ≠ 2*h by omega]
  intro d hd hp
  by_cases hm : 3*h ≤ d
  · exact hm
  · have hp1 := hp h
    have hp2 := hp (2*h)
    rw [hfh,hf (h+d)] at hp1
    have hmem : (h+d)%(3*h)=h ∨ (h+d)%(3*h)=2*h := by
      by_cases hmem : (h+d)%(3*h)=h ∨ (h+d)%(3*h)=2*h
      · exact hmem
      · rw [if_neg hmem] at hp1; exact False.elim (hne hp1.symm)
    have hdEq : d=h := by
      by_cases hlt : h+d < 3*h
      · rw [Nat.mod_eq_of_lt hlt] at hmem; omega
      · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at hmem; omega
    rw [hdEq,show 2*h+h=3*h by omega,hf0,hf2] at hp2
    exact False.elim (hne hp2.symm)

/-- At the least period, the half-modulus family disappears entirely. -/
theorem least_period_classification {m : Nat} (hm : 0 < m) (h3 : m%3=0)
    {f : Nat → α} (hp : HasPeriod f m)
    (hmin : ∀ d, 0 < d → HasPeriod f d → m ≤ d) :
    ExactlyTwo m f ↔ ThirdShape m f := by
  constructor
  · intro he
    rcases (two_defect_classification hm h3 hp).mp he with hhalf|hthird
    · obtain ⟨d,hd,hdm,hdp⟩ := half_shape_smaller_period hm hhalf
      have := hmin d hd hdp; omega
    · exact hthird
  · intro hs; exact (two_defect_classification hm h3 hp).mpr (Or.inr hs)

open Collatz.Sum

private theorem three_terms_le {N i j k : Nat} (w : Nat → Nat)
    (hi : i < N) (hj : j < N) (hk : k < N)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    w i+w j+w k ≤ sumRange N w := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [sumRange_succ]
    by_cases hiN : i < N
    · by_cases hjN : j < N
      · by_cases hkN : k < N
        · have := ih hiN hjN hkN; omega
        · have hkEq : k=N := by omega
          have := PeriodicSingleDefect.two_terms_le w hiN hjN hij
          subst k; omega
      · have hjEq : j=N := by omega
        have := PeriodicSingleDefect.two_terms_le w hiN (by omega : k < N) hik
        subst j; omega
    · have hiEq : i=N := by omega
      have := PeriodicSingleDefect.two_terms_le w (by omega : j < N) (by omega : k < N) hjk
      subst i; omega

/-- Equivalence with the repository's actual finite defect count. -/
theorem count_eq_two_iff {m : Nat} (hm : 0 < m) {f : Nat → Bool}
    (hp : HasPeriod f m) : defectCount m f=2 ↔ ExactlyTwo m f := by
  classical
  let w := fun n => if Defect f n then 1 else 0
  have hw : sumRange (2*m) w=defectCount m f := by
    unfold defectCount
    apply sumRange_congr
    intro n _
    dsimp [w,Defect]
    split <;> simp_all
  constructor
  · intro hcount
    have hex : ∃ r, r < 2*m ∧ Defect f r := by
      apply Classical.byContradiction
      intro hn
      have hz : sumRange (2*m) w=0 := by
        calc
          _ = sumRange (2*m) (fun _ => 0) := sumRange_congr (fun n h => by
            have hh : ¬Defect f n := fun hd => hn ⟨n,h,hd⟩
            simp [w,hh])
          _ = 0 := by rw [sumRange_const,Nat.mul_zero]
      omega
    obtain ⟨r,hr,hdr⟩ := hex
    have hex2 : ∃ s, s < 2*m ∧ s ≠ r ∧ Defect f s := by
      apply Classical.byContradiction
      intro hn
      have hsingle : ∀ n, n < 2*m → Defect f n → n=r := by
        intro n hn' hd
        by_cases he : n=r
        · exact he
        · exact False.elim (hn ⟨n,hn',he,hd⟩)
      have hone := TreeStochastic.sumRange_indicator_one (Defect f) hr hdr hsingle
      change sumRange (2*m) w=1 at hone
      omega
    obtain ⟨s,hs,hsr,hds⟩ := hex2
    refine ⟨r,s,hr,hs,Ne.symm hsr,?_⟩
    intro n
    rw [period_mod (defect_period hp) n]
    constructor
    · intro hd
      by_cases hr' : n%(2*m)=r
      · exact Or.inl hr'
      · by_cases hs' : n%(2*m)=s
        · exact Or.inr hs'
        · have hsum := three_terms_le w (Nat.mod_lt n (by omega)) hr hs hr' hs' (Ne.symm hsr)
          have hwr : w r=1 := by simp [w,hdr]
          have hws : w s=1 := by simp [w,hds]
          have hwn : w (n%(2*m))=1 := by simp [w,hd]
          rw [hwr,hws,hwn,hw,hcount] at hsum
          omega
    · intro hn
      rcases hn with hn|hn
      · rw [hn]; exact hdr
      · rw [hn]; exact hds
  · rintro ⟨r,s,hr,hs,hrs,hex⟩
    have hsum : sumRange (2*m) w =
        sumRange (2*m) (fun n => if n=r then 1 else 0) +
        sumRange (2*m) (fun n => if n=s then 1 else 0) := by
      rw [← sumRange_add]
      apply sumRange_congr
      intro n hn
      have hh := hex n
      rw [Nat.mod_eq_of_lt hn] at hh
      dsimp [w]
      by_cases hnr : n=r <;> by_cases hns : n=s <;> simp_all
    have hr1 := TreeStochastic.sumRange_indicator_one (fun n => n=r) hr rfl (fun _ _ h => h)
    have hs1 := TreeStochastic.sumRange_indicator_one (fun n => n=s) hs rfl (fun _ _ h => h)
    rw [hr1,hs1,hw] at hsum
    exact hsum

/-- The counted version of the complete classification. -/
theorem counted_classification {m : Nat} (hm : 0 < m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    defectCount m f=2 ↔ HalfShape m f ∨ ThirdShape m f := by
  rw [count_eq_two_iff hm hp,two_defect_classification hm h3 hp]

/-- A residue of an integer prime to three cannot be divisible by three. -/
theorem residue_off_three {m n r : Nat} (h3 : m%3=0) (hn : n%3 ≠ 0)
    (hr : r%3=0) : n%m ≠ r := by
  intro he
  have hh := Nat.mod_mod_of_dvd n (Nat.dvd_of_mod_eq_zero h3)
  rw [he,hr] at hh
  exact hn hh.symm

/-- Every two-defect label is constant on integers not divisible by three. -/
theorem two_defects_constant_off_three {m : Nat} (hm : 0 < m) (h3 : m%3=0)
    {f : Nat → α} (hp : HasPeriod f m) (he : ExactlyTwo m f) :
    ∀ a b, a%3 ≠ 0 → b%3 ≠ 0 → f a=f b := by
  have hs := (two_defect_classification hm h3 hp).mp he
  rcases hs with ⟨h,A,B,hmEq,_,hf⟩ | ⟨h,A,B,hmEq,hh3,_,hf⟩
  · subst m
    have hh3 : h%3=0 := by omega
    intro a b ha hb
    simp only [hf a,hf b,
      residue_off_three h3 ha (by decide : 0%3=0),residue_off_three h3 ha hh3,
      residue_off_three h3 hb (by decide : 0%3=0),residue_off_three h3 hb hh3,
      false_or,if_false]
  · subst m
    have h2h3 : (2*h)%3=0 := by omega
    intro a b ha hb
    simp only [hf a,hf b,residue_off_three h3 ha hh3,residue_off_three h3 ha h2h3,
      residue_off_three h3 hb hh3,residue_off_three h3 hb h2h3,false_or,if_false]

/-- Sharp lower bound for any Boolean label distinguishing nonmultiples of three. -/
theorem three_le_of_separates_off_three {m : Nat} (hm : 0 < m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) {a b : Nat}
    (ha : a%3 ≠ 0) (hb : b%3 ≠ 0) (hne : f a ≠ f b) :
    3 ≤ defectCount m f := by
  have hpos := defectCount_positive hm hp ⟨a,b,hne⟩
  by_cases hone : defectCount m f=1
  · obtain ⟨_,_,hf⟩ := (one_defect_iff_all (by omega : 1 < m) hp).mp hone
    have hfa : f a=f 1 := by rw [hf a,if_neg (residue_off_three h3 ha (by decide))]
    have hfb : f b=f 1 := by rw [hf b,if_neg (residue_off_three h3 hb (by decide))]
    exact False.elim (hne (hfa.trans hfb.symm))
  · by_cases htwo : defectCount m f=2
    · exact False.elim (hne (two_defects_constant_off_three hm h3 hp
        ((count_eq_two_iff hm hp).mp htwo) a b ha hb))
    · omega

/-- A uniform sharpness witness: the singleton residue one. -/
def oneLabel (m n : Nat) : Bool := decide (n%m=1)

theorem oneLabel_period (m : Nat) : HasPeriod (oneLabel m) m := by
  intro n; simp [oneLabel]

/-- The three defective inputs of the singleton-one label, at every multiple of three. -/
theorem oneLabel_positions {m : Nat} (hm : 0 < m) (h3 : m%3=0) (n : Nat) :
    Defect (oneLabel m) n ↔ n%(2*m)=1 ∨ n%(2*m)=2 ∨ n%(2*m)=m+1 := by
  have hm1 : 1 < m := by omega
  have hf : ∀ n, oneLabel m n=if n%m=1 then true else false := by
    intro n; simp [oneLabel]
  rw [two_label_defect (by decide : true ≠ false) hf,
    preimage_residue hm h3 hm1 (by decide),residue_lifts hm hm1]
  simp only [Nat.mul_one]
  omega

/-- The sharp bound three is attained for every positive modulus divisible by three. -/
theorem oneLabel_count {m : Nat} (hm : 0 < m) (h3 : m%3=0) :
    defectCount m (oneLabel m)=3 := by
  have hm3 : 3 ≤ m := by omega
  let w := fun n => if (n=1) then 1 else 0
  let v := fun n => if (n=2) then 1 else 0
  let z := fun n => if (n=m+1) then 1 else 0
  have hh : defectCount m (oneLabel m)=sumRange (2*m) (fun n => w n+v n+z n) := by
    apply sumRange_congr
    intro n hn
    have hp := oneLabel_positions hm h3 n
    rw [Nat.mod_eq_of_lt hn] at hp
    change (oneLabel m (acceleratedStep n) ≠ oneLabel m n ↔ _) at hp
    dsimp [w,v,z]
    by_cases h1 : n=1 <;> by_cases h2 : n=2 <;> by_cases h3' : n=m+1 <;>
      simp_all
  rw [hh,sumRange_add,sumRange_add]
  have h1 := TreeStochastic.sumRange_indicator_one (fun n => n=1)
    (by omega : 1 < 2*m) rfl (fun _ _ h => h)
  have h2 := TreeStochastic.sumRange_indicator_one (fun n => n=2)
    (by omega : 2 < 2*m) rfl (fun _ _ h => h)
  have h3' := TreeStochastic.sumRange_indicator_one (fun n => n=m+1)
    (by omega : m+1 < 2*m) rfl (fun _ _ h => h)
  change sumRange (2*m) w=1 at h1
  change sumRange (2*m) v=1 at h2
  change sumRange (2*m) z=1 at h3'
  omega

/-- A single statement combines the universal lower bound with uniform attainment. -/
theorem sharp_core_minimum {m : Nat} (hm : 0 < m) (h3 : m%3=0) :
    (∀ f : Nat → Bool, HasPeriod f m →
      (∃ a b, a%3 ≠ 0 ∧ b%3 ≠ 0 ∧ f a ≠ f b) → 3 ≤ defectCount m f) ∧
    HasPeriod (oneLabel m) m ∧ oneLabel m 1 ≠ oneLabel m 2 ∧
      defectCount m (oneLabel m)=3 := by
  refine ⟨?_,oneLabel_period m,?_,oneLabel_count hm h3⟩
  · intro f hp ⟨a,b,ha,hb,hne⟩
    exact three_le_of_separates_off_three hm h3 hp ha hb hne
  · have hm3 : 3 ≤ m := by omega
    simp [oneLabel,Nat.mod_eq_of_lt (by omega : 1 < m),Nat.mod_eq_of_lt (by omega : 2 < m)]

end Collatz.PeriodicTwoDefectAll
