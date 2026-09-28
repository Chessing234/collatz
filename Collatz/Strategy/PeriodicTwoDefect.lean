import Collatz.Strategy.PeriodicSingleDefect

/-!
Two affine defects in a doubling-invariant periodic label.
This is a finite residue theorem; it makes no convergence assertion.
-/
namespace Collatz.PeriodicTwoDefect
open PeriodicRigidity PeriodicSingleDefect

def AffineDefect (f : Nat → α) (n : Nat) : Prop := f (3 * n + 1) ≠ f n

theorem fibre_image {f : Nat → α} {h : Nat} (hp : HasPeriod f (3*h)) (n k : Nat) :
    f (3*(n+k*h)+1) = f (3*n+1) := by
  have he : 3*(n+k*h)+1 = (3*n+1)+k*(3*h) := by
    simp only [Nat.mul_add, Nat.mul_left_comm]; omega
  rw [he, period_mul hp]

theorem double_mates {f : Nat → α} {h d : Nat} (hp : HasPeriod f (3*h))
    (h2 : ∀ n, f (2*n) = f n)
    (h1 : f (d+h) = f (3*d+1)) (h2' : f (d+2*h) = f (3*d+1)) :
    f (2*d+h) = f (3*d+1) ∧ f (2*d+2*h) = f (3*d+1) := by
  constructor
  · calc
      f (2*d+h) = f (2*d+h+3*h) := (hp _).symm
      _ = f (2*(d+2*h)) := by congr 1; omega
      _ = f (d+2*h) := h2 _
      _ = f (3*d+1) := h2'
  · calc
      f (2*d+2*h) = f (2*(d+h)) := by congr 1; omega
      _ = f (d+h) := h2 _
      _ = f (3*d+1) := h1

/-- Two exceptional residues must belong to the same three-element fibre. -/
theorem same_fibre {f : Nat → α} {h p q : Nat} (hh : 0 < h) (hodd : (3*h)%2 = 1)
    (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n)
    (hpbound : p < 3*h) (hqbound : q < 3*h) (hne : p ≠ q)
    (hex : ∀ n, AffineDefect f n ↔ n % (3*h) = p ∨ n % (3*h) = q) :
    p % h = q % h := by
  classical
  apply Classical.byContradiction
  intro hfibre
  have hred : ∀ n, n % (3*h) % h = n % h := fun n =>
    Nat.mod_mod_of_dvd n (Nat.dvd_mul_left h 3)
  have hregular : ∀ n, n % (3*h) ≠ p → n % (3*h) ≠ q → f (3*n+1) = f n := by
    intro n hnp hnq
    exact Classical.byContradiction (fun hn => (hex n).mp hn |>.elim hnp hnq)
  have hdoubles : ∀ d e, d < 3*h → e < 3*h → d % h ≠ e % h →
      (∀ n, AffineDefect f n ↔ n % (3*h) = d ∨ n % (3*h) = e) →
      (2*d) % (3*h) = d ∨ (2*d) % (3*h) = e := by
    intro d e hd he hde hx
    have reg : ∀ n, n % (3*h) ≠ d → n % (3*h) ≠ e → f (3*n+1) = f n := by
      intro n hnd hne'
      exact Classical.byContradiction (fun hn => (hx n).mp hn |>.elim hnd hne')
    have mate : ∀ k, 0 < k → k < 3 → f (d+k*h) = f (3*d+1) := by
      intro k hk hk3
      have hkcases : k = 1 ∨ k = 2 := by omega
      have hpos : 0 < k*h := Nat.mul_pos hk hh
      have hlt : k*h < 3*h := Nat.mul_lt_mul_of_pos_right hk3 hh
      have hnD : (d+k*h) % (3*h) ≠ d := by
        have ht := shift_mod_ne (m := 3*h) hpos hlt d
        rwa [Nat.mod_eq_of_lt hd] at ht
      have hnE : (d+k*h) % (3*h) ≠ e := by
        intro hn
        have ht := hred (d+k*h)
        rw [hn] at ht
        simp only [Nat.add_mul_mod_self_right] at ht
        exact hde ht.symm
      exact (reg _ hnD hnE).symm.trans (fibre_image hp d k)
    have hm1 := mate 1 (by decide) (by decide)
    simp only [Nat.one_mul] at hm1
    obtain ⟨hdb1,hdb2⟩ := double_mates hp h2 hm1 (mate 2 (by decide) (by decide))
    by_cases hdd : AffineDefect f (2*d)
    · exact (hx _).mp hdd
    have hr : f (3*(2*d)+1) = f (2*d) := Classical.byContradiction hdd
    have bad : ∀ k, k = 1 ∨ k = 2 → AffineDefect f (2*d+k*h) := by
      intro k hk hgood
      have hl : f (2*d+k*h) = f (3*d+1) := by
        rcases hk with rfl | rfl
        · simpa using hdb1
        · exact hdb2
      have hb : AffineDefect f d := (hx d).mpr (Or.inl (Nat.mod_eq_of_lt hd))
      exact hb (hl.symm.trans (hgood.symm.trans
        ((fibre_image hp (2*d) k).trans (hr.trans (h2 d)))))
    have b1 := (hx _).mp (bad 1 (Or.inl rfl))
    have b2 := (hx _).mp (bad 2 (Or.inr rfl))
    have neq : (2*d+2*h) % (3*h) ≠ (2*d+h) % (3*h) := by
      simpa [Nat.add_assoc, show h+h=2*h by omega] using
        shift_mod_ne (m := 3*h) hh (by omega) (2*d+h)
    have eqfib : (2*d+1*h) % (3*h) % h = (2*d+2*h) % (3*h) % h := by
      rw [hred, hred]; simp
    rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2
    · simp only [Nat.one_mul] at b1; exact False.elim (neq (b2.trans b1.symm))
    · rw [b1,b2] at eqfib; exact False.elim (hde eqfib)
    · rw [b1,b2] at eqfib; exact False.elim (hde eqfib.symm)
    · simp only [Nat.one_mul] at b1; exact False.elim (neq (b2.trans b1.symm))
  have dp := hdoubles p q hpbound hqbound hfibre hex
  have dq := hdoubles q p hqbound hpbound (Ne.symm hfibre) (by
    intro n; rw [hex, or_comm])
  have unfoldmod : ∀ d, d < 3*h → 2*d = (2*d) % (3*h) ∨ 2*d = (2*d) % (3*h) + 3*h := by
    intro d hd
    by_cases hb : 2*d < 3*h
    · exact Or.inl (Nat.mod_eq_of_lt hb).symm
    · right; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have up := unfoldmod p hpbound
  have uq := unfoldmod q hqbound
  have hvals : (p = h ∧ q = 2*h) ∨ (p = 2*h ∧ q = h) := by omega
  rcases hvals with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp at hfibre


theorem affine_reduce {f : Nat → α} {h : Nat} (hp : HasPeriod f (3*h)) (n : Nat) :
    f (3*n+1) = f (3*(n%h)+1) := by
  have hn : n = n%h + (n/h)*h := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div n h).symm
  conv => lhs; rw [hn]
  exact fibre_image hp (n%h) (n/h)

/-- The two exceptional residues are exactly one third and two thirds of the period. -/
theorem defect_locations {f : Nat → α} {h p q : Nat} (hh : 0 < h) (hodd : (3*h)%2 = 1)
    (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n)
    (hpbound : p < 3*h) (hqbound : q < 3*h) (hne : p ≠ q)
    (hex : ∀ n, AffineDefect f n ↔ n % (3*h) = p ∨ n % (3*h) = q) :
    (p = h ∧ q = 2*h) ∨ (p = 2*h ∧ q = h) := by
  classical
  have hf := same_fibre hh hodd hp h2 hpbound hqbound hne hex
  have hred : ∀ n, n % (3*h) % h = n % h := fun n =>
    Nat.mod_mod_of_dvd n (Nat.dvd_mul_left h 3)
  have hpbad : AffineDefect f p := (hex p).mpr (Or.inl (Nat.mod_eq_of_lt hpbound))
  have hm1 : (p+h) % (3*h) ≠ p := by
    simpa [Nat.mod_eq_of_lt hpbound] using shift_mod_ne (m := 3*h) hh (by omega) p
  have hm2 : (p+2*h) % (3*h) ≠ p := by
    simpa [Nat.mod_eq_of_lt hpbound] using
      shift_mod_ne (m := 3*h) (by omega : 0 < 2*h) (by omega) p
  have hdistinct : (p+2*h) % (3*h) ≠ (p+h) % (3*h) := by
    simpa [Nat.add_assoc, show h+h=2*h by omega] using
      shift_mod_ne (m := 3*h) hh (by omega) (p+h)
  have hexr : ∃ r, r % h = p % h ∧ f (3*p+1) = f r := by
    by_cases hq1 : (p+h) % (3*h) = q
    · refine ⟨p+2*h, by simp, ?_⟩
      have hr : ¬ AffineDefect f (p+2*h) := by
        rw [hex]; exact fun he => he.elim hm2 (fun he => hdistinct (he.trans hq1.symm))
      exact (fibre_image hp p 2).symm.trans (Classical.byContradiction hr)
    · refine ⟨p+h, by simp, ?_⟩
      have hr : ¬ AffineDefect f (p+h) := by
        rw [hex]; exact fun he => he.elim hm1 hq1
      have hi := fibre_image hp p 1
      simp only [Nat.one_mul] at hi
      exact hi.symm.trans (Classical.byContradiction hr)
  obtain ⟨r, hrmod, hrlabel⟩ := hexr
  have hne2 : f (2*p) ≠ f (2*r) := by
    rw [h2,h2]; exact fun he => hpbad (hrlabel.trans he.symm)
  have heqmod : (2*p) % h = (2*r) % h := by
    rw [← Nat.mul_mod_mod, ← Nat.mul_mod_mod 2 r, hrmod]
  have heqimage : f (3*(2*p)+1) = f (3*(2*r)+1) := by
    rw [affine_reduce hp (2*p), affine_reduce hp (2*r), heqmod]
  have hb : AffineDefect f (2*p) ∨ AffineDefect f (2*r) := by
    by_cases hb1 : AffineDefect f (2*p)
    · exact Or.inl hb1
    · right; intro hb2
      exact hne2 ((Classical.byContradiction hb1).symm.trans (heqimage.trans hb2))
  have hdmod : (2*p) % h = p % h := by
    rcases hb with hb | hb
    · rcases (hex _).mp hb with hd | hd
      · have ht := hred (2*p); rw [hd] at ht; exact ht.symm
      · have ht := hred (2*p); rw [hd, ← hf] at ht; exact ht.symm
    · rw [heqmod]
      rcases (hex _).mp hb with hd | hd
      · have ht := hred (2*r); rw [hd] at ht; exact ht.symm
      · have ht := hred (2*r); rw [hd, ← hf] at ht; exact ht.symm
  have hpzero : p % h = 0 := by
    have hb := Nat.mod_lt p hh
    rw [← Nat.mul_mod_mod] at hdmod
    by_cases ht : 2*(p%h) < h
    · rw [Nat.mod_eq_of_lt ht] at hdmod; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hdmod; omega
  have hqzero : q % h = 0 := hf.symm.trans hpzero
  have three : ∀ d, d < 3*h → d % h = 0 → d = 0 ∨ d = h ∨ d = 2*h := by
    intro d hd hz
    by_cases h1 : d < h
    · rw [Nat.mod_eq_of_lt h1] at hz; exact Or.inl hz
    · rw [Nat.mod_eq_sub_mod (by omega)] at hz
      by_cases h2' : d-h < h
      · rw [Nat.mod_eq_of_lt h2'] at hz; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hz; omega
  have pv := three p hpbound hpzero
  have qv := three q hqbound hqzero
  have hdiff : AffineDefect f h ↔ AffineDefect f (2*h) := by
    unfold AffineDefect
    rw [affine_reduce hp h, affine_reduce hp (2*h), h2 h]
    simp
  rw [hex,hex, Nat.mod_eq_of_lt (by omega : h < 3*h),
    Nat.mod_eq_of_lt (by omega : 2*h < 3*h)] at hdiff
  omega


/-- Doubling permutes the two nonzero thirds when the period is odd. -/
theorem double_thirds {h n : Nat} (hh : 0 < h) (hodd : (3*h)%2 = 1) :
    ((2*n)%(3*h) = h ∨ (2*n)%(3*h) = 2*h) ↔
      (n%(3*h) = h ∨ n%(3*h) = 2*h) := by
  rw [← Nat.mul_mod_mod]
  have hb := Nat.mod_lt n (by omega : 0 < 3*h)
  by_cases ht : 2*(n%(3*h)) < 3*h
  · rw [Nat.mod_eq_of_lt ht]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem affine_avoids_thirds {h n : Nat} (h3 : h%3 = 0) :
    ¬ ((3*n+1)%(3*h) = h ∨ (3*n+1)%(3*h) = 2*h) := by
  have hr := Nat.mod_mod_of_dvd (3*n+1) (Nat.dvd_mul_right 3 h)
  intro he
  rcases he with he | he <;> rw [he] at hr <;> omega

/-- Complete label rigidity for a period divisible by nine. -/
theorem label_rigidity {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2 = 1) (h3 : h%3 = 0)
    (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n)
    (hex : ∀ n, AffineDefect f n ↔ n%(3*h) = h ∨ n%(3*h) = 2*h) :
    f h ≠ f 1 ∧ ∀ n, f n = if n%(3*h) = h ∨ n%(3*h) = 2*h then f h else f 1 := by
  classical
  have hi : f (3*h+1) = f 1 := by simpa [Nat.add_comm] using hp 1
  have hbad : f h ≠ f 1 := by
    have hb := (hex h).mpr (Or.inl (Nat.mod_eq_of_lt (by omega)))
    exact Ne.symm (hi ▸ hb)
  let g := fun n => if n%(3*h) = h ∨ n%(3*h) = 2*h then f 1 else f n
  have hgp : HasPeriod g (3*h) := by intro n; simp [g,hp n]
  have hg2 : ∀ n, g (2*n) = g n := by
    intro n; simp only [g, double_thirds hh hodd, h2 n]
  have hg3 : ∀ n, g (3*n+1) = g n := by
    intro n
    dsimp [g]
    rw [if_neg (affine_avoids_thirds h3)]
    by_cases hn : n%(3*h) = h ∨ n%(3*h) = 2*h
    · rw [if_pos hn, period_mod hp (3*n+1)]
      have hr : (3*n+1)%(3*h) = 1 := by
        rw [Nat.add_mod, ← Nat.mul_mod_mod 3 n]
        rcases hn with hn | hn <;> rw [hn] <;>
          simp [show 3*(2*h)=2*(3*h) by omega, Nat.mod_eq_of_lt (by omega : 1 < 3*h)]
      rw [hr]
    · rw [if_neg hn]
      exact Classical.byContradiction (fun he => hn ((hex n).mp he))
  have hc := branch_rigidity (3*h) (by omega) g hgp hg2 (fun n _ => hg3 n)
  have hg0 : g 0 = f 1 := by
    have hreg : f 1 = f 0 := by
      apply Classical.byContradiction
      intro he
      have hb := (hex 0).mp he
      simp at hb
      omega
    simp [g,hreg]
  refine ⟨hbad, ?_⟩
  intro n
  by_cases hn : n%(3*h) = h ∨ n%(3*h) = 2*h
  · rw [if_pos hn, period_mod hp n]
    rcases hn with hn | hn
    · rw [hn]
    · rw [hn]; exact h2 h
  · rw [if_neg hn]
    have ht := (hc n).trans hg0
    simpa [g,hn] using ht

/-- A nonempty, uniform family: precisely the two nonzero thirds carry the
exceptional value. This proves the classification is attained at every odd
multiple of nine, rather than being a vacuous necessary condition. -/
theorem two_defects_iff {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2 = 1) (h3 : h%3 = 0)
    (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n) :
    (∃ p q, p < 3*h ∧ q < 3*h ∧ p ≠ q ∧
      ∀ n, AffineDefect f n ↔ n%(3*h) = p ∨ n%(3*h) = q) ↔
    f h ≠ f 1 ∧ ∀ n, f n = if n%(3*h) = h ∨ n%(3*h) = 2*h then f h else f 1 := by
  constructor
  · rintro ⟨p,q,hp',hq',hne,hex⟩
    have loc := defect_locations hh hodd hp h2 hp' hq' hne hex
    apply label_rigidity hh hodd h3 hp h2
    rcases loc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hex
    · intro n; rw [hex,or_comm]
  · rintro ⟨hne,hform⟩
    refine ⟨h,2*h,by omega,by omega,by omega,?_⟩
    intro n
    unfold AffineDefect
    rw [hform (3*n+1), if_neg (affine_avoids_thirds h3), hform n]
    by_cases hn : n%(3*h) = h ∨ n%(3*h) = 2*h <;> simp [hn, Ne.symm hne]


/-- A second factor of three is necessary, not just sufficient. -/
theorem nine_necessary {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2 = 1) (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n)
    (hex : ∀ n, AffineDefect f n ↔ n%(3*h) = h ∨ n%(3*h) = 2*h) : h%3 = 0 := by
  classical
  apply Classical.byContradiction
  intro hnot
  have exceptional : ∀ n, n%(3*h) = h ∨ n%(3*h) = 2*h → f (3*n+1) = f 1 := by
    intro n hn
    rw [period_mod hp (3*n+1)]
    have hr : (3*n+1)%(3*h) = 1 := by
      rw [Nat.add_mod, ← Nat.mul_mod_mod 3 n]
      rcases hn with hn | hn <;> rw [hn] <;>
        simp [show 3*(2*h)=2*(3*h) by omega, Nat.mod_eq_of_lt (by omega : 1 < 3*h)]
    rw [hr]
  have regular : ∀ n, ¬ (n%(3*h) = h ∨ n%(3*h) = 2*h) → f (3*n+1) = f n := by
    intro n hn
    exact Classical.byContradiction (fun he => hn ((hex n).mp he))
  have bad : f h ≠ f 1 := by
    have he := (hex h).mpr (Or.inl (Nat.mod_eq_of_lt (by omega)))
    unfold AffineDefect at he
    rw [exceptional h (Or.inl (Nat.mod_eq_of_lt (by omega)))] at he
    exact Ne.symm he
  let g := fun n => f (3*n+1)
  have gp : HasPeriod g h := by
    intro n; exact (by simpa using fibre_image hp n 1)
  have g2 : ∀ n, g (2*n) = g n := by
    intro n
    change f (3*(2*n)+1) = f (3*n+1)
    by_cases hn : n%(3*h) = h ∨ n%(3*h) = 2*h
    · rw [exceptional n hn, exceptional (2*n) ((double_thirds hh hodd).mpr hn)]
    · rw [regular n hn, regular (2*n) (fun he => hn ((double_thirds hh hodd).mp he)),h2]
  have g3 : ∀ n, g n = f 1 → g (3*n+1) = f 1 := by
    intro n he
    change f (3*(3*n+1)+1) = f 1
    by_cases ht : (3*n+1)%(3*h) = h ∨ (3*n+1)%(3*h) = 2*h
    · exact exceptional _ ht
    · exact (regular _ ht).trans he
  let w := fun n => decide (g n = f 1)
  have wp : HasPeriod w h := by intro n; simp [w,gp n]
  have closed : ∀ n, w n = true → w (acceleratedStep n) = true := by
    intro n hn
    have he : g n = f 1 := by simpa [w] using hn
    have ht : g (acceleratedStep n) = f 1 := by
      by_cases heven : n%2 = 0
      · have hs : acceleratedStep n = n/2 := by simp [acceleratedStep,heven]
        rw [hs, ← g2 (n/2), show 2*(n/2)=n by omega]; exact he
      · have hs : acceleratedStep n = (3*n+1)/2 := by simp [acceleratedStep,heven]
        rw [hs, ← g2 ((3*n+1)/2), show 2*((3*n+1)/2)=3*n+1 by omega]
        exact g3 n he
    simpa [w] using ht
  have ex0 : PeriodicDefectMinimum.exitCount h w = 0 := by
    unfold PeriodicDefectMinimum.exitCount
    have hz : ∀ n, ¬ (w n = true ∧ w (acceleratedStep n) = false) := by
      intro n ⟨hn,ht⟩; have hc := closed n hn; rw [hc] at ht; cases ht
    simp only [hz,if_false,Sum.sumRange_const,Nat.mul_zero]
  have dc0 : PeriodicDefectMinimum.defectCount h w = 0 := by
    rw [PeriodicDefectMinimum.defects_twice_exits hh hnot wp,ex0]
  have wc : ∀ n, w n = w 0 := by
    intro n
    apply Classical.byContradiction
    intro hn
    have hc := PeriodicDefectMinimum.defectCount_positive hh wp ⟨n,0,hn⟩
    omega
  have gc : ∀ n, g n = f 1 := by
    intro n
    have hw := wc n
    have wz : w 0 = true := by simp [w,g]
    rw [wz] at hw
    simpa [w] using hw
  have hcases : h%3 = 1 ∨ h%3 = 2 := by omega
  rcases hcases with hc | hc
  · have hn : 3*((h-1)/3)+1 = h := by omega
    have he := gc ((h-1)/3)
    change f (3*((h-1)/3)+1) = f 1 at he
    rw [hn] at he; exact bad he
  · have hn : 3*((2*h-1)/3)+1 = 2*h := by omega
    have he := gc ((2*h-1)/3)
    change f (3*((2*h-1)/3)+1) = f 1 at he
    rw [hn,h2] at he; exact bad he

/-- Classification at every odd period divisible by three, with no assumed
second factor of three. -/
theorem two_defects_iff_all {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2 = 1) (hp : HasPeriod f (3*h)) (h2 : ∀ n, f (2*n) = f n) :
    (∃ p q, p < 3*h ∧ q < 3*h ∧ p ≠ q ∧
      ∀ n, AffineDefect f n ↔ n%(3*h) = p ∨ n%(3*h) = q) ↔
    h%3 = 0 ∧ f h ≠ f 1 ∧
      ∀ n, f n = if n%(3*h) = h ∨ n%(3*h) = 2*h then f h else f 1 := by
  constructor
  · rintro ⟨p,q,hp',hq',hne,hex⟩
    have loc := defect_locations hh hodd hp h2 hp' hq' hne hex
    have he : ∀ n, AffineDefect f n ↔ n%(3*h) = h ∨ n%(3*h) = 2*h := by
      rcases loc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hex
      · intro n; rw [hex,or_comm]
    have h3 := nine_necessary hh hodd hp h2 he
    exact ⟨h3,label_rigidity hh hodd h3 hp h2 he⟩
  · rintro ⟨h3,hform⟩
    exact (two_defects_iff hh hodd h3 hp h2).mpr hform
end Collatz.PeriodicTwoDefect
