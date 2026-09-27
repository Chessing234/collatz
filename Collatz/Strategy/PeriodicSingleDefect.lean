import Collatz.Strategy.PeriodicDefectMinimum

/-!
Rigidity of one-error labels under doubling and the affine odd branch.
The three lifts of a residue provide redundancy: a unique exceptional lift
must be preserved by doubling, which forces it to be the zero residue.
-/

namespace Collatz.PeriodicSingleDefect

open PeriodicRigidity

theorem shift_mod_ne {m s : Nat} (hs : 0 < s) (hsm : s < m) (n : Nat) :
    (n + s) % m ≠ n % m := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt hsm]
  have hr : n % m < m := Nat.mod_lt _ (by omega)
  by_cases h : n % m + s < m
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- If an odd-period label is invariant under doubling, and the affine branch
has exactly one exceptional residue, then that residue is zero and every
nonzero residue has the same label. -/
theorem affine_single_defect {α : Type} {f : Nat → α} {h d : Nat}
    (hh : 0 < h) (hodd : (3 * h) % 2 = 1) (hd : d < 3 * h)
    (hp : HasPeriod f (3 * h)) (h2 : ∀ n, f (2 * n) = f n)
    (hexact : ∀ n, (f (3 * n + 1) ≠ f n ↔ n % (3 * h) = d)) :
    d = 0 ∧ ∀ n, n % (3 * h) ≠ 0 → f n = f 1 := by
  classical
  have hregular : ∀ n, n % (3 * h) ≠ d → f (3 * n + 1) = f n := by
    intro n hn
    exact Classical.byContradiction (fun he => hn ((hexact n).mp he))
  have himage : ∀ n k, f (3 * (n + k * h) + 1) = f (3 * n + 1) := by
    intro n k
    have he : 3 * (n + k * h) + 1 = (3 * n + 1) + k * (3 * h) := by
      simp only [Nat.mul_add, Nat.mul_left_comm]
      omega
    rw [he, period_mul hp]
  have hbase : f (3 * d + 1) ≠ f d := (hexact d).mpr (Nat.mod_eq_of_lt hd)
  have hmate1 : f (d + h) = f (3 * d + 1) := by
    have hr := hregular (d + h) (by
      have he := shift_mod_ne (m := 3 * h) hh (by omega) d
      rwa [Nat.mod_eq_of_lt hd] at he)
    have hs := himage d 1
    simp only [Nat.one_mul] at hs
    exact hr.symm.trans hs
  have hmate2 : f (d + 2 * h) = f (3 * d + 1) := by
    have hr := hregular (d + 2 * h) (by
      have he := shift_mod_ne (m := 3 * h) (by omega : 0 < 2 * h) (by omega) d
      rwa [Nat.mod_eq_of_lt hd] at he)
    exact hr.symm.trans (himage d 2)
  have hdouble1 : f (2 * d + h) = f (3 * d + 1) := by
    calc
      f (2 * d + h) = f (2 * d + h + 3 * h) := (hp _).symm
      _ = f (2 * (d + 2 * h)) := by congr 1; omega
      _ = f (d + 2 * h) := h2 _
      _ = f (3 * d + 1) := hmate2
  have hdouble2 : f (2 * d + 2 * h) = f (3 * d + 1) := by
    calc
      f (2 * d + 2 * h) = f (2 * (d + h)) := by congr 1; omega
      _ = f (d + h) := h2 _
      _ = f (3 * d + 1) := hmate1
  have hfixed : (2 * d) % (3 * h) = d := by
    apply Classical.byContradiction
    intro hn
    have hroot := hregular (2 * d) hn
    have hdistinct : (2 * d + 2 * h) % (3 * h) ≠ (2 * d + h) % (3 * h) := by
      simpa [Nat.add_assoc, show h + h = 2 * h by omega] using
        shift_mod_ne (m := 3 * h) hh (by omega) (2 * d + h)
    have one_good : (2 * d + h) % (3 * h) ≠ d ∨ (2 * d + 2 * h) % (3 * h) ≠ d := by
      by_cases hz : (2 * d + h) % (3 * h) = d
      · exact Or.inr (fun hz' => hdistinct (hz'.trans hz.symm))
      · exact Or.inl hz
    rcases one_good with hg | hg
    · have hr := hregular (2 * d + h) hg
      have hs := himage (2 * d) 1
      simp only [Nat.one_mul] at hs
      exact hbase (hdouble1.symm.trans (hr.symm.trans (hs.trans (hroot.trans (h2 d)))))
    · have hr := hregular (2 * d + 2 * h) hg
      exact hbase (hdouble2.symm.trans
        (hr.symm.trans ((himage (2 * d) 2).trans (hroot.trans (h2 d)))))
  have hd0 : d = 0 := by
    by_cases he : 2 * d < 3 * h
    · rw [Nat.mod_eq_of_lt he] at hfixed; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hfixed
      omega
  refine ⟨hd0, ?_⟩
  subst d
  have hzero : ∀ n, (2 * n) % (3 * h) = 0 ↔ n % (3 * h) = 0 := by
    intro n
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    exact ⟨(LocalBlindness.coprime_two_of_odd hodd).dvd_of_dvd_mul_left,
      fun hn => Nat.dvd_mul_left_of_dvd hn 2⟩
  have hnotzero : ∀ n, (3 * n + 1) % (3 * h) ≠ 0 := by
    intro n hn
    have hdvd : 3 ∣ 3 * n + 1 := Nat.dvd_trans (Nat.dvd_mul_right 3 h)
      (Nat.dvd_of_mod_eq_zero hn)
    have := Nat.mod_eq_zero_of_dvd hdvd
    omega
  let g := fun n => if n % (3 * h) = 0 then f 1 else f n
  have hgp : HasPeriod g (3 * h) := by
    intro n; simp [g, hp n]
  have hg2 : ∀ n, g (2 * n) = g n := by
    intro n; simp only [g, hzero n, h2 n]
  have hg3 : ∀ n, g (3 * n + 1) = g n := by
    intro n
    dsimp [g]
    rw [if_neg (hnotzero n)]
    by_cases hn : n % (3 * h) = 0
    · rw [if_pos hn, period_mod hp (3 * n + 1)]
      have hmod : (3 * n + 1) % (3 * h) = 1 := by
        rw [Nat.add_mod, Nat.mul_mod, hn]
        simp [Nat.mod_eq_of_lt (by omega : 1 < 3 * h)]
      rw [hmod]
    · rw [if_neg hn]
      exact hregular n hn
  have hconst := branch_rigidity (3 * h) (by omega) g hgp hg2 (fun n _ => hg3 n)
  intro n hn
  have hc := hconst n
  simpa [g, hn] using hc

/-- An odd modulus makes doubling a permutation. A unique defect cannot lie
on a doubling cycle, since it would be the sole change of label on that cycle. -/
theorem doubling_invariant_of_single_defect {α : Type} {f : Nat → α} {m r : Nat}
    (hm : 0 < m) (hodd : m % 2 = 1) (hp : HasPeriod f m)
    (hexact : ∀ n, Defect f n ↔ n % (2 * m) = r) :
    ∀ n, f (2 * n) = f n := by
  classical
  have htp : HasPeriod (fun n => f (acceleratedStep n)) (2 * m) := by
    intro n
    dsimp
    rw [step_add_even]
    split
    · exact hp _
    · exact period_mul hp _ 3
  have hout : ∀ n, Defect f n → f (acceleratedStep n) = f (acceleratedStep r) := by
    intro n hn
    have h := period_mod htp n
    simpa [(hexact n).mp hn] using h
  have heven : ∀ n, acceleratedStep (2 * n) = n := by intro n; simp [acceleratedStep]
  obtain ⟨e, he, hemod⟩ := LocalBlindness.exists_pow_one_mod hm (by decide : 0 < 2)
    (LocalBlindness.coprime_two_of_odd hodd).symm
  intro n
  apply Classical.byContradiction
  intro hn
  have hdn : Defect f (2 * n) := by simpa [Defect, heven] using Ne.symm hn
  have hbase : f n = f (acceleratedStep r) := by simpa [heven] using hout _ hdn
  have stay : ∀ x, f x = f (2 * n) → f (2 * x) = f (2 * n) := by
    intro x hx
    by_cases hchange : f (2 * x) = f x
    · exact hchange.trans hx
    · have hdx : Defect f (2 * x) := by simpa [Defect, heven] using Ne.symm hchange
      have hxbase : f x = f (acceleratedStep r) := by simpa [heven] using hout _ hdx
      exact False.elim (hn (hx.symm.trans (hxbase.trans hbase.symm)))
  have hchain : ∀ k, f (2 ^ (k + 1) * n) = f (2 * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ (k + 1)) 2, Nat.mul_assoc]
      exact stay _ ih
  have hreturn : f (2 ^ e * n) = f n := by
    rw [period_mod hp (2 ^ e * n), period_mod hp n, Nat.mul_mod, hemod]
    simp
  have heq : e = (e - 1) + 1 := by omega
  have h := hchain (e - 1)
  rw [← heq, hreturn] at h
  exact hn h.symm

theorem odd_lift_unique {m r n : Nat} (hm : 0 < m) (hodd : m % 2 = 1)
    (hr : r < 2 * m) (hro : r % 2 = 1) (hno : n % 2 = 1) :
    n % (2 * m) = r ↔ n % m = r % m := by
  have hn2 : n % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  have hpar : n % (2 * m) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (Nat.dvd_mul_right 2 m), hno]
  have hred : n % (2 * m) % m = n % m :=
    Nat.mod_mod_of_dvd n (Nat.dvd_mul_left m 2)
  rw [← hred]
  generalize n % (2 * m) = t at *
  constructor
  · intro h; rw [h]
  · intro h
    by_cases ha : t < m <;> by_cases hb : r < m
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h; exact h
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb] at h
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : m ≤ t), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega : m ≤ r), Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- Classification of all single-defect labels at odd moduli divisible by 3.
Apart from renaming the two labels, the only example is divisibility by m. -/
theorem single_defect_rigidity {α : Type} {f : Nat → α} {h r : Nat}
    (hh : 0 < h) (hodd : (3 * h) % 2 = 1) (hr : r < 2 * (3 * h))
    (hp : HasPeriod f (3 * h))
    (hexact : ∀ n, Defect f n ↔ n % (2 * (3 * h)) = r) :
    r = 3 * h ∧ f 0 ≠ f 1 ∧ ∀ n, n % (3 * h) ≠ 0 → f n = f 1 := by
  have hm : 0 < 3 * h := by omega
  have h2 := doubling_invariant_of_single_defect hm hodd hp hexact
  have hdr : Defect f r := (hexact r).mpr (Nat.mod_eq_of_lt hr)
  have hrpos : 0 < r := by
    by_cases hz : r = 0
    · subst r; simp [Defect] at hdr
    · omega
  have hro : r % 2 = 1 := by
    by_cases he : r % 2 = 0
    · have hs : acceleratedStep r = r / 2 := by simp [acceleratedStep, he]
      have h := h2 (r / 2)
      have heq : 2 * (r / 2) = r := by omega
      rw [heq] at h
      exact False.elim (hdr (by rw [hs]; exact h.symm))
    · omega
  have odd_branch : ∀ n, n % 2 = 1 →
      (f (3 * n + 1) ≠ f n ↔ n % (3 * h) = r % (3 * h)) := by
    intro n hn
    have hs : 2 * acceleratedStep n = 3 * n + 1 := by
      unfold acceleratedStep; rw [if_neg (by omega)]; omega
    have hf : f (3 * n + 1) = f (acceleratedStep n) := by rw [← hs, h2]
    rw [hf]
    exact (hexact n).trans (odd_lift_unique hm hodd hr hro hn)
  have affine_exact : ∀ n, f (3 * n + 1) ≠ f n ↔ n % (3 * h) = r % (3 * h) := by
    intro n
    by_cases hn : n % 2 = 1
    · exact odd_branch n hn
    · have hb := odd_branch (n + 3 * h) (by omega)
      have he : 3 * (n + 3 * h) + 1 = (3 * n + 1) + 3 * (3 * h) := by omega
      rw [he, period_mul hp _ 3, hp n, Nat.add_mod_right] at hb
      exact hb
  obtain ⟨hz, hc⟩ := affine_single_defect hh hodd (Nat.mod_lt r hm) hp h2 affine_exact
  have hrm : r = 3 * h := by
    have hz' := (PeriodicDefectMinimum.residue_zero_iff hm hr).mp hz
    omega
  refine ⟨hrm, ?_, hc⟩
  have hd0 : f 1 ≠ f 0 := by simpa using (affine_exact 0).mpr (by simpa using hz.symm)
  exact Ne.symm hd0

open Collatz.Sum PeriodicDefectMinimum

theorem two_terms_le {N i j : Nat} (w : Nat → Nat)
    (hi : i < N) (hj : j < N) (hne : i ≠ j) : w i + w j ≤ sumRange N w := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [sumRange_succ]
    by_cases hiN : i < N <;> by_cases hjN : j < N
    · have := ih hiN hjN; omega
    · have hjEq : j = N := by omega
      have := le_sumRange w hiN
      subst j; omega
    · have hiEq : i = N := by omega
      have := le_sumRange w hjN
      subst i; omega
    · omega

theorem progression_of_count_one {m : Nat} (hm : 0 < m) {f : Nat → Bool}
    (hp : HasPeriod f m) (hne : ∃ a b, f a ≠ f b) (hcount : defectCount m f = 1) :
    ∃ r, r < 2 * m ∧ ∀ n, Defect f n ↔ n % (2 * m) = r := by
  obtain ⟨r, _, hr, hprog⟩ := defect_progression hm hp hne
  have hdr : Defect f r := by simpa using hprog 0
  refine ⟨r, hr, ?_⟩
  intro n
  have hred := period_mod (defect_period hp) n
  rw [hred]
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hneq
    have h := two_terms_le
      (fun n => if f (acceleratedStep n) = f n then 0 else 1)
      (Nat.mod_lt n (by omega : 0 < 2 * m)) hr hneq
    change f (acceleratedStep (n % (2 * m))) ≠ f (n % (2 * m)) at hn
    change f (acceleratedStep r) ≠ f r at hdr
    rw [if_neg hn, if_neg hdr] at h
    change 1 + 1 ≤ defectCount m f at h
    omega
  · intro hn; rw [hn]; exact hdr

/-- Complete classification at every odd modulus: exactly one defect occurs
iff 3 divides m and the zero residue alone has a different Boolean label. -/
theorem one_defect_iff {m : Nat} (hm : 1 < m) (hodd : m % 2 = 1)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    defectCount m f = 1 ↔ m % 3 = 0 ∧ f 0 ≠ f 1 ∧
      ∀ n, f n = if n % m = 0 then f 0 else f 1 := by
  classical
  constructor
  · intro hcount
    have hne : ∃ a b, f a ≠ f b := by
      apply Classical.byContradiction
      intro hn
      have heq : ∀ n, f (acceleratedStep n) = f n := by
        intro n
        exact Classical.byContradiction (fun h => hn ⟨acceleratedStep n, n, h⟩)
      have hz : defectCount m f = 0 := by
        unfold defectCount
        simp only [heq, if_true]
        rw [sumRange_const, Nat.mul_zero]
      omega
    have h3 : m % 3 = 0 := by
      by_cases h : m % 3 = 0
      · exact h
      · have := two_le_defectCount (by omega) h hp hne; omega
    obtain ⟨r, hr, hexact⟩ := progression_of_count_one (by omega) hp hne hcount
    have hclass : f 0 ≠ f 1 ∧ ∀ n, n % m ≠ 0 → f n = f 1 := by
      obtain ⟨h, hmEq⟩ := Nat.dvd_of_mod_eq_zero h3
      subst m
      exact (single_defect_rigidity (by omega) hodd hr hp hexact).2
    refine ⟨h3, hclass.1, ?_⟩
    intro n
    by_cases hn : n % m = 0
    · rw [if_pos hn, period_mod hp n, hn]
    · rw [if_neg hn]; exact hclass.2 n hn
  · rintro ⟨h3, hneq, hform⟩
    have heq : defectCount m f = defectCount m (divisibleLabel m) := by
      unfold defectCount
      apply sumRange_congr
      intro n _
      rw [hform (acceleratedStep n), hform n]
      unfold divisibleLabel
      by_cases ht : acceleratedStep n % m = 0 <;> by_cases hn : n % m = 0 <;>
        simp [ht, hn, hneq, Ne.symm hneq]
    rw [heq, divisibleLabel_defectCount hm, if_pos h3]

end Collatz.PeriodicSingleDefect
