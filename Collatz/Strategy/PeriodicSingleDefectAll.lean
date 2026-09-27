import Collatz.Strategy.PeriodicSingleDefect

/-!
Doubling a modulus preserves the classification of single-defect labels.
The graph at modulus 2M is the directed line graph of the graph at M.
The proof below uses explicit residue edges rather than a graph library.
-/

namespace Collatz.PeriodicSingleDefectAll

open PeriodicRigidity PeriodicDefectMinimum PeriodicSingleDefect

theorem two_lifts {M a b : Nat} (_hM : 0 < M) (ha : a < 2 * M) (hb : b < 2 * M)
    (he : a % M = b % M) : a = b ∨ (a + M) % (2 * M) = b := by
  by_cases haM : a < M <;> by_cases hbM : b < M
  · left; rwa [Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hbM] at he
  · right
    rw [Nat.mod_eq_of_lt haM, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at he
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hbM] at he
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · left
    rw [Nat.mod_eq_sub_mod (by omega : M ≤ a), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_sub_mod (by omega : M ≤ b), Nat.mod_eq_of_lt (by omega)] at he
    omega

/-- Every pair of composable residue edges lifts to an actual step. -/
theorem composable_lift {M a b : Nat} (hM : 0 < M) (ha : a < 2 * M) (hb : b < 2 * M)
    (he : acceleratedStep a % M = b % M) :
    ∃ u, u < 2 * (2 * M) ∧ u % (2 * M) = a ∧ acceleratedStep u % (2 * M) = b := by
  have ht : acceleratedStep a % (2 * M) < 2 * M := Nat.mod_lt _ (by omega)
  have hred : acceleratedStep a % (2 * M) % M = b % M := by
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left M 2), he]
  rcases two_lifts hM ht hb hred with h | h
  · exact ⟨a, by omega, Nat.mod_eq_of_lt ha, h⟩
  · refine ⟨a + 2 * M, by omega, ?_, ?_⟩
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · have hflip : (acceleratedStep a + M) % (2 * M) = b := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : M < 2 * M)]
        exact h
      rw [step_add_even]
      split
      · exact hflip
      · rw [show acceleratedStep a + 3 * M = (acceleratedStep a + M) + 2 * M by omega,
          Nat.add_mod_right]
        exact hflip

theorem output_period (M : Nat) : HasPeriod (fun n => acceleratedStep n % M) (2 * M) := by
  intro n
  dsimp
  rw [step_add_even]
  split
  · simp
  · simp [Nat.add_mod]

/-- The only edge entering zero is the zero loop when 3 divides the modulus. -/
theorem target_zero {M a : Nat} (_hM : 0 < M) (h3 : M % 3 = 0)
    (ha : a < 2 * M) (hz : acceleratedStep a % M = 0) : a = 0 := by
  by_cases he : a % 2 = 0
  · have hs : acceleratedStep a = a / 2 := by simp [acceleratedStep, he]
    rw [hs, Nat.mod_eq_of_lt (by omega)] at hz
    omega
  · have hs3 : acceleratedStep a % 3 = 2 := by
      unfold acceleratedStep; rw [if_neg he]; omega
    have hd : 3 ∣ acceleratedStep a := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h3)
      (Nat.dvd_of_mod_eq_zero hz)
    have := Nat.mod_eq_zero_of_dvd hd
    omega

/-- A unique defect at modulus 2M induces a unique defect at modulus M.
The induced label is the label of the canonical incoming even edge. -/
theorem descend_single_defect {α : Type} {f : Nat → α} {M r : Nat}
    (hM : 0 < M) (hr : r < 2 * (2 * M)) (hp : HasPeriod f (2 * M))
    (hexact : ∀ n, Defect f n ↔ n % (2 * (2 * M)) = r) :
    let g := fun n => f (2 * (n % M))
    HasPeriod g M ∧
    (∀ a, a < 2 * M → f a = g (acceleratedStep a)) ∧
    (∀ n, Defect g n ↔ n % (2 * M) = acceleratedStep r % (2 * M)) ∧
    (∀ a b, a < 2 * M → b < 2 * M → acceleratedStep a % M = b % M →
      f a ≠ f b → a = r % (2 * M) ∧ b = acceleratedStep r % (2 * M)) := by
  classical
  let g := fun n => f (2 * (n % M))
  have hgp : HasPeriod g M := by intro n; simp [g]
  have hpair : ∀ a b, a < 2 * M → b < 2 * M → acceleratedStep a % M = b % M →
      f a ≠ f b → a = r % (2 * M) ∧ b = acceleratedStep r % (2 * M) := by
    intro a b ha hb he hne
    obtain ⟨u, hu, hua, hub⟩ := composable_lift hM ha hb he
    have hdu : Defect f u := by
      unfold Defect
      rw [period_mod hp (acceleratedStep u), period_mod hp u, hua, hub]
      exact Ne.symm hne
    have hur := (hexact u).mp hdu
    rw [Nat.mod_eq_of_lt hu] at hur
    subst u
    exact ⟨hua.symm, hub.symm⟩
  have heven : ∀ n, acceleratedStep (2 * n) = n := by intro n; simp [acceleratedStep]
  have hlabel : ∀ a, a < 2 * M → f a = g (acceleratedStep a) := by
    intro a ha
    let v := acceleratedStep a % M
    have hv : v < M := Nat.mod_lt _ hM
    let b := if v = acceleratedStep r % (2 * M) then v + M else v
    have hb : b < 2 * M := by dsimp [b]; split <;> omega
    have hbmod : b % M = v := by
      dsimp [b]
      split
      · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hv]
      · exact Nat.mod_eq_of_lt hv
    have hbne : b ≠ acceleratedStep r % (2 * M) := by dsimp [b]; split <;> omega
    have hab : f a = f b := by
      apply Classical.byContradiction
      intro hn
      exact hbne (hpair a b ha hb hbmod.symm hn).2
    have hcb : f (2 * v) = f b := by
      apply Classical.byContradiction
      intro hn
      have he : acceleratedStep (2 * v) % M = b % M := by
        rw [heven, Nat.mod_eq_of_lt hv, hbmod]
      exact hbne (hpair (2 * v) b (by omega) hb he hn).2
    exact hab.trans hcb.symm
  let a0 := r % (2 * M)
  let b0 := acceleratedStep r % (2 * M)
  have ha0 : a0 < 2 * M := Nat.mod_lt _ (by omega)
  have hb0 : b0 < 2 * M := Nat.mod_lt _ (by omega)
  have hcompose : acceleratedStep a0 % M = b0 % M := by
    have h := period_mod (output_period M) r
    dsimp [a0, b0]
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left M 2)]
    exact h.symm
  have hbad : f b0 ≠ f a0 := by
    have hd := (hexact r).mpr (Nat.mod_eq_of_lt hr)
    unfold Defect at hd
    rwa [period_mod hp (acceleratedStep r), period_mod hp r] at hd
  have hga : g b0 = f a0 := by
    rw [hlabel a0 ha0]
    dsimp [g]
    rw [hcompose]
  have hlocal : ∀ a, a < 2 * M → (Defect g a ↔ a = b0) := by
    intro a ha
    constructor
    · intro hd
      have hn : f (2 * (a % M)) ≠ f a := by
        intro he
        apply hd
        rw [← hlabel a ha]
        exact he.symm
      have he : acceleratedStep (2 * (a % M)) % M = a % M := by
        rw [heven, Nat.mod_mod]
      exact (hpair (2 * (a % M)) a (by have := Nat.mod_lt a hM; omega) ha he hn).2
    · intro he; subst a
      change g (acceleratedStep b0) ≠ g b0
      rw [← hlabel b0 hb0, hga]
      exact hbad
  refine ⟨hgp, hlabel, ?_, hpair⟩
  intro n
  rw [period_mod (defect_period hgp) n]
  exact hlocal _ (Nat.mod_lt _ (by omega))

/-- Every modulus divisible by 3 has just one possible single-defect cut:
the zero residue is separated from all other residues. -/
theorem all_single_defect {α : Type} (m : Nat) (hm : 0 < m) (h3 : m % 3 = 0)
    (f : Nat → α) (r : Nat) (hr : r < 2 * m) (hp : HasPeriod f m)
    (hexact : ∀ n, Defect f n ↔ n % (2 * m) = r) :
    r = m ∧ f 0 ≠ f 1 ∧ ∀ n, n % m ≠ 0 → f n = f 1 := by
  induction m using Nat.strongRecOn generalizing f r with
  | ind m ih =>
    by_cases he : m % 2 = 0
    · obtain ⟨M, hmEq⟩ : ∃ M, m = 2 * M := ⟨m / 2, by omega⟩
      subst m
      have hM : 0 < M := by omega
      have hM3 : M % 3 = 0 := by omega
      let g := fun n => f (2 * (n % M))
      obtain ⟨hgp, hlabel, hgexact, hpair⟩ := descend_single_defect hM hr hp hexact
      obtain ⟨hb0, hgne, hgc⟩ := ih M (by omega) hM hM3 g
        (acceleratedStep r % (2 * M)) (Nat.mod_lt _ (by omega)) hgp hgexact
      have h0 : f 0 = g 0 := by simp [g]
      have hdm : Defect g M := (hgexact M).mpr (by rw [Nat.mod_eq_of_lt (by omega), hb0])
      have hfne : f 0 ≠ f M := by
        intro h
        apply hdm
        calc
          g (acceleratedStep M) = f M := (hlabel M (by omega)).symm
          _ = f 0 := h.symm
          _ = g 0 := h0
          _ = g M := by simp [g]
      have hrzero : r % (2 * M) = 0 :=
        (hpair 0 M (by omega) (by omega) (by simp) hfne).1.symm
      have hrne : r ≠ 0 := by
        intro h
        have hd := (hexact r).mpr (Nat.mod_eq_of_lt hr)
        simp [h, Defect] at hd
      have hrm : r = 2 * M := by
        have := (residue_zero_iff (by omega : 0 < 2 * M) hr).mp hrzero
        omega
      have hothers : ∀ n, n % (2 * M) ≠ 0 → f n = g 1 := by
        intro n hn
        have ha : n % (2 * M) < 2 * M := Nat.mod_lt _ (by omega)
        have htarget : acceleratedStep (n % (2 * M)) % M ≠ 0 := by
          intro hz
          exact hn (target_zero hM hM3 ha hz)
        calc
          f n = f (n % (2 * M)) := period_mod hp n
          _ = g (acceleratedStep (n % (2 * M))) := hlabel _ ha
          _ = g 1 := hgc _ htarget
      have h1 : f 1 = g 1 := hothers 1 (by rw [Nat.mod_eq_of_lt (by omega)]; decide)
      refine ⟨hrm, ?_, fun n hn => (hothers n hn).trans h1.symm⟩
      intro heq
      exact hgne (h0.symm.trans (heq.trans h1))
    · have hodd : m % 2 = 1 := by omega
      obtain ⟨h, hmEq⟩ := Nat.dvd_of_mod_eq_zero h3
      subst m
      exact single_defect_rigidity (by omega) hodd hr hp hexact

/-- Complete, all-modulus classification of Boolean labels with one defect. -/
theorem one_defect_iff_all {m : Nat} (hm : 1 < m) {f : Nat → Bool}
    (hp : HasPeriod f m) :
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
        rw [Collatz.Sum.sumRange_const, Nat.mul_zero]
      omega
    have h3 : m % 3 = 0 := by
      by_cases h : m % 3 = 0
      · exact h
      · have := two_le_defectCount (by omega) h hp hne; omega
    obtain ⟨r, hr, hexact⟩ := progression_of_count_one (by omega) hp hne hcount
    obtain ⟨_, hneq, hc⟩ := all_single_defect m (by omega) h3 f r hr hp hexact
    refine ⟨h3, hneq, ?_⟩
    intro n
    by_cases hn : n % m = 0
    · rw [if_pos hn, period_mod hp n, hn]
    · rw [if_neg hn]; exact hc n hn
  · rintro ⟨h3, hneq, hform⟩
    have heq : defectCount m f = defectCount m (divisibleLabel m) := by
      unfold defectCount
      apply Collatz.Sum.sumRange_congr
      intro n _
      rw [hform (acceleratedStep n), hform n]
      unfold divisibleLabel
      by_cases ht : acceleratedStep n % m = 0 <;> by_cases hn : n % m = 0 <;>
        simp [ht, hn, hneq, Ne.symm hneq]
    rw [heq, divisibleLabel_defectCount hm, if_pos h3]

end Collatz.PeriodicSingleDefectAll
