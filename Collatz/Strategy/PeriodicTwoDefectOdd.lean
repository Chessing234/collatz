import Collatz.Strategy.PeriodicTwoDefect

/-! Removing the doubling-invariance hypothesis for two Collatz defects. -/
namespace Collatz.PeriodicTwoDefectOdd
open PeriodicRigidity PeriodicSingleDefect PeriodicTwoDefect

/-- A unique exceptional even edge cannot occur around a doubling cycle. -/
theorem no_unique_even {f : Nat → α} {m r : Nat} (hm : 0 < m)
    (hodd : m%2 = 1) (hp : HasPeriod f m)
    (hu : ∀ n, n%2 = 0 → Defect f n → n%(2*m) = r) :
    ∀ n, f (2*n) = f n := by
  classical
  have htp : HasPeriod (fun n => f (acceleratedStep n)) (2*m) := by
    intro n
    dsimp
    rw [step_add_even]
    split
    · exact hp _
    · exact period_mul hp _ 3
  have hout : ∀ n, n%2 = 0 → Defect f n → f (acceleratedStep n) = f (acceleratedStep r) := by
    intro n he hn
    have ht := period_mod htp n
    simpa [hu n he hn] using ht
  have heven : ∀ n, acceleratedStep (2*n) = n := by intro n; simp [acceleratedStep]
  obtain ⟨e,he,hemod⟩ := LocalBlindness.exists_pow_one_mod hm (by decide : 0 < 2)
    (LocalBlindness.coprime_two_of_odd hodd).symm
  intro n
  apply Classical.byContradiction
  intro hn
  have hdn : Defect f (2*n) := by simpa [Defect,heven] using Ne.symm hn
  have hbase : f n = f (acceleratedStep r) := by simpa [heven] using hout _ (by omega) hdn
  have stay : ∀ x, f x = f (2*n) → f (2*x) = f (2*n) := by
    intro x hx
    by_cases hc : f (2*x) = f x
    · exact hc.trans hx
    · have hdx : Defect f (2*x) := by simpa [Defect,heven] using Ne.symm hc
      have hxb : f x = f (acceleratedStep r) := by simpa [heven] using hout _ (by omega) hdx
      exact False.elim (hn (hx.symm.trans (hxb.trans hbase.symm)))
  have chain : ∀ k, f (2^(k+1)*n) = f (2*n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ,Nat.mul_comm (2^(k+1)) 2,Nat.mul_assoc]
      exact stay _ ih
  have hret : f (2^e*n) = f n := by
    rw [period_mod hp (2^e*n),period_mod hp n,Nat.mul_mod,hemod]; simp
  have hh := chain (e-1)
  rw [show e-1+1=e by omega,hret] at hh
  exact hn hh.symm

/-- If all odd edges preserve a label, its period loses a factor of three. -/
theorem period_third {f : Nat → α} {h : Nat} (hodd : (3*h)%2 = 1)
    (hp : HasPeriod f (3*h)) (ho : ∀ n, n%2 = 1 → f (acceleratedStep n) = f n) :
    HasPeriod f h := by
  have oddcase : ∀ n, n%2 = 1 → f (n+h) = f n := by
    intro n hn
    have ht := ho (n+2*(2*h)) (by omega)
    rw [step_add_even,if_neg (by omega : ¬n%2=0)] at ht
    have hs : f (acceleratedStep n + 3*(2*h)) = f (acceleratedStep n) := by
      have he : 3*(2*h) = 2*(3*h) := by omega
      rw [he,period_mul hp]
    rw [hs,ho n hn] at ht
    have hr : f (n+2*(2*h)) = f (n+h) := by
      have he : n+2*(2*h) = n+h+3*h := by omega
      rw [he,hp]
    rw [hr] at ht; exact ht.symm
  intro n
  by_cases hn : n%2 = 1
  · exact oddcase n hn
  · have ht := oddcase (n+3*h) (by omega)
    rw [show n+3*h+h=n+h+3*h by omega,hp,hp] at ht
    exact ht

/-- Three repeated defects cannot fit into two distinct exceptional classes. -/
theorem cannot_period_third {f : Nat → α} {h r s : Nat} (hh : 0 < h)
    (hp : HasPeriod f h) (hr : r < 6*h)
    (hex : ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s) : False := by
  have hb : Defect f r := (hex r).mpr (Or.inl (Nat.mod_eq_of_lt hr))
  have hperiod := defect_period hp
  have b1 : Defect f (r+2*h) := by rw [hperiod]; exact hb
  have b2 : Defect f (r+2*(2*h)) := by rw [period_mul hperiod]; exact hb
  have h1 := (hex _).mp b1
  have h2 := (hex _).mp b2
  have ne1 : (r+2*h)%(6*h) ≠ r := by
    simpa [Nat.mod_eq_of_lt hr] using shift_mod_ne (m:=6*h) (by omega : 0 < 2*h) (by omega) r
  have ne2 : (r+2*(2*h))%(6*h) ≠ r := by
    simpa [Nat.mod_eq_of_lt hr] using shift_mod_ne (m:=6*h) (by omega : 0 < 2*(2*h)) (by omega) r
  have ne12 : (r+2*(2*h))%(6*h) ≠ (r+2*h)%(6*h) := by
    have he : r+2*(2*h) = (r+2*h)+2*h := by omega
    rw [he]
    exact shift_mod_ne (m:=6*h) (by omega) (by omega) (r+2*h)
  exact ne12 ((h2.resolve_left ne2).trans (h1.resolve_left ne1).symm)

/-- With precisely two defects, both must be odd edges. -/
theorem doubling_invariant {f : Nat → α} {h r s : Nat} (hh : 0 < h)
    (hodd : (3*h)%2 = 1) (hp : HasPeriod f (3*h))
    (hr : r < 6*h) (_hs : s < 6*h)
    (hex : ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s) :
    ∀ n, f (2*n) = f n := by
  have hpar : ∀ n, n%(6*h)%2 = n%2 := fun n =>
    Nat.mod_mod_of_dvd n (by exact ⟨3*h,by omega⟩)
  by_cases hrOdd : r%2=1
  · apply no_unique_even (m:=3*h) (r:=s) (by omega) hodd hp
    intro n hn hd
    have he := (hex n).mp hd
    have ht := hpar n
    rcases he with he | he
    · rw [he,hrOdd,hn] at ht; contradiction
    · simpa [show 2*(3*h)=6*h by omega] using he
  · by_cases hsOdd : s%2=1
    · apply no_unique_even (m:=3*h) (r:=r) (by omega) hodd hp
      intro n hn hd
      have he := (hex n).mp hd
      have ht := hpar n
      rcases he with he | he
      · simpa [show 2*(3*h)=6*h by omega] using he
      · rw [he,hsOdd,hn] at ht; contradiction
    · have ho : ∀ n, n%2=1 → f (acceleratedStep n) = f n := by
        intro n hn
        apply Classical.byContradiction
        intro hd
        have he := (hex n).mp hd
        have ht := hpar n
        rcases he with he | he <;> rw [he,hn] at ht <;> omega
      exact False.elim (cannot_period_third hh (period_third hodd hp ho) hr hex)


theorem odd_defect_affine {f : Nat → α} (h2 : ∀ n, f (2*n) = f n)
    {n : Nat} (hn : n%2=1) : Defect f n ↔ AffineDefect f n := by
  have he : 2*((3*n+1)/2)=3*n+1 := by omega
  unfold Defect AffineDefect
  rw [show acceleratedStep n = (3*n+1)/2 by simp [acceleratedStep,hn],
    ← h2 ((3*n+1)/2),he]

theorem defect_odd {f : Nat → α} (h2 : ∀ n, f (2*n) = f n)
    {n : Nat} (hd : Defect f n) : n%2=1 := by
  by_cases he : n%2=0
  · have hs : acceleratedStep n = n/2 := by simp [acceleratedStep,he]
    have ht := h2 (n/2)
    rw [show 2*(n/2)=n by omega] at ht
    exact False.elim (hd (hs ▸ ht.symm))
  · omega

/-- The two original Collatz error classes induce two distinct affine errors. -/
theorem affine_pair {f : Nat → α} {m r s : Nat} (hm : 0 < m)
    (hodd : m%2=1) (hp : HasPeriod f m) (h2 : ∀ n, f (2*n) = f n)
    (hr : r < 2*m) (hs : s < 2*m) (hne : r ≠ s)
    (hex : ∀ n, Defect f n ↔ n%(2*m)=r ∨ n%(2*m)=s) :
    r%m ≠ s%m ∧ ∀ n, AffineDefect f n ↔ n%m=r%m ∨ n%m=s%m := by
  have hrOdd := defect_odd h2 ((hex r).mpr (Or.inl (Nat.mod_eq_of_lt hr)))
  have hsOdd := defect_odd h2 ((hex s).mpr (Or.inr (Nat.mod_eq_of_lt hs)))
  have different : r%m ≠ s%m := by
    intro he
    have ht := (odd_lift_unique hm hodd hs hsOdd hrOdd).mpr he
    rw [Nat.mod_eq_of_lt hr] at ht
    exact hne ht
  have oddcase : ∀ n, n%2=1 → (AffineDefect f n ↔ n%m=r%m ∨ n%m=s%m) := by
    intro n hn
    rw [← odd_defect_affine h2 hn,hex,odd_lift_unique hm hodd hr hrOdd hn,
      odd_lift_unique hm hodd hs hsOdd hn]
  refine ⟨different,?_⟩
  intro n
  by_cases hn : n%2=1
  · exact oddcase n hn
  · have ht := oddcase (n+m) (by omega)
    have he : AffineDefect f (n+m) ↔ AffineDefect f n := by
      unfold AffineDefect
      rw [show 3*(n+m)+1=(3*n+1)+3*m by omega,period_mul hp,hp]
    simpa [he] using ht

/-- Exact defect positions for the classified labels. -/
theorem exact_positions {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2=1) (h2 : ∀ n, f (2*n) = f n)
    (hex : ∀ n, AffineDefect f n ↔ n%(3*h)=h ∨ n%(3*h)=2*h) :
    ∀ n, Defect f n ↔ n%(6*h)=h ∨ n%(6*h)=5*h := by
  have hhOdd : h%2=1 := by omega
  intro n
  by_cases hn : n%2=1
  · rw [odd_defect_affine h2 hn,hex]
    have ha := odd_lift_unique (by omega : 0 < 3*h) hodd
      (by omega : h < 2*(3*h)) hhOdd hn
    have hb := odd_lift_unique (by omega : 0 < 3*h) hodd
      (by omega : 5*h < 2*(3*h)) (by omega : (5*h)%2=1) hn
    rw [Nat.mod_eq_of_lt (by omega : h < 3*h)] at ha
    have hmod : (5*h)%(3*h)=2*h := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
    rw [hmod] at hb
    simpa [show 2*(3*h)=6*h by omega] using or_congr ha.symm hb.symm
  · have hd : ¬ Defect f n := fun hd => hn (defect_odd h2 hd)
    have hr := Nat.mod_mod_of_dvd n (show 2 ∣ 6*h from ⟨3*h,by omega⟩)
    have hrange : ¬ (n%(6*h)=h ∨ n%(6*h)=5*h) := by
      intro he; rcases he with he | he <;> rw [he] at hr <;> omega
    simp [hd,hrange]

/-- Complete two-defect classification for every odd modulus divisible by 3.
Labels may take values in any type; the conclusion forces exactly two values. -/
theorem two_defect_classification {f : Nat → α} {h : Nat} (hh : 0 < h)
    (hodd : (3*h)%2=1) (hp : HasPeriod f (3*h)) :
    (∃ r s, r < 6*h ∧ s < 6*h ∧ r ≠ s ∧
      ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s) ↔
    h%3=0 ∧ f h ≠ f 1 ∧
      ∀ n, f n = if n%(3*h)=h ∨ n%(3*h)=2*h then f h else f 1 := by
  constructor
  · rintro ⟨r,s,hr,hs,hne,hex⟩
    have h2 := doubling_invariant hh hodd hp hr hs hex
    have he : ∀ n, Defect f n ↔ n%(2*(3*h))=r ∨ n%(2*(3*h))=s := by
      simpa [show 2*(3*h)=6*h by omega] using hex
    obtain ⟨hdiff,hpair⟩ := affine_pair (by omega : 0 < 3*h) hodd hp h2
      (by omega) (by omega) hne he
    exact (two_defects_iff_all hh hodd hp h2).mp
      ⟨r%(3*h),s%(3*h),Nat.mod_lt _ (by omega),Nat.mod_lt _ (by omega),hdiff,hpair⟩
  · rintro ⟨h3,hne,hform⟩
    have h2 : ∀ n, f (2*n)=f n := by
      intro n; rw [hform (2*n),hform n]; simp only [double_thirds hh hodd]
    have ha : ∀ n, AffineDefect f n ↔ n%(3*h)=h ∨ n%(3*h)=2*h := by
      intro n
      unfold AffineDefect
      rw [hform (3*n+1),if_neg (affine_avoids_thirds h3),hform n]
      by_cases hn : n%(3*h)=h ∨ n%(3*h)=2*h <;> simp [hn,Ne.symm hne]
    exact ⟨h,5*h,by omega,by omega,by omega,exact_positions hh hodd h2 ha⟩


/-- Such a Boolean label exists precisely when nine divides the odd period. -/
theorem exists_two_iff_nine {h : Nat} (hh : 0 < h) (hodd : (3*h)%2=1) :
    (∃ f : Nat → Bool, HasPeriod f (3*h) ∧
      ∃ r s, r < 6*h ∧ s < 6*h ∧ r ≠ s ∧
        ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s) ↔ h%3=0 := by
  constructor
  · rintro ⟨f,hp,he⟩
    exact ((two_defect_classification hh hodd hp).mp he).1
  · intro h3
    let f := fun n => decide (n%(3*h)=h ∨ n%(3*h)=2*h)
    have hp : HasPeriod f (3*h) := by intro n; simp [f]
    refine ⟨f,hp,(two_defect_classification hh hodd hp).mpr ⟨h3,?_,?_⟩⟩
    · have hh' : 1 < h := by omega
      simp [f,Nat.mod_eq_of_lt (by omega : h < 3*h),
        Nat.mod_eq_of_lt (by omega : 1 < 3*h),show 1 ≠ h by omega,show 1 ≠ 2*h by omega]
    · intro n
      have hh' : 1 < h := by omega
      simp only [f,Nat.mod_eq_of_lt (by omega : h < 3*h),true_or,decide_true,
        Nat.mod_eq_of_lt (by omega : 1 < 3*h)]
      by_cases hn : n%(3*h)=h ∨ n%(3*h)=2*h <;>
        simp [hn,show 1 ≠ h by omega,show 1 ≠ 2*h by omega]


/-- The original two Collatz error classes are uniquely determined. -/
theorem positions_of_two {f : Nat → α} {h r s : Nat} (hh : 0 < h)
    (hodd : (3*h)%2=1) (hp : HasPeriod f (3*h))
    (hr : r < 6*h) (hs : s < 6*h) (hne : r ≠ s)
    (hex : ∀ n, Defect f n ↔ n%(6*h)=r ∨ n%(6*h)=s) :
    ∀ n, Defect f n ↔ n%(6*h)=h ∨ n%(6*h)=5*h := by
  have h2 := doubling_invariant hh hodd hp hr hs hex
  obtain ⟨h3,hbad,hform⟩ := (two_defect_classification hh hodd hp).mp ⟨r,s,hr,hs,hne,hex⟩
  apply exact_positions hh hodd h2
  intro n
  unfold AffineDefect
  rw [hform (3*n+1),if_neg (affine_avoids_thirds h3),hform n]
  by_cases hn : n%(3*h)=h ∨ n%(3*h)=2*h <;> simp [hn,Ne.symm hbad]
end Collatz.PeriodicTwoDefectOdd
