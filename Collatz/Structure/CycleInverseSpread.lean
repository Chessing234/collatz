import Collatz.Structure.CycleMaxClass

/-!
# Residue-sensitive cycle spread from forced inverse branches

A cycle contains no multiples of three. At targets congruent to 1 modulo 3,
there is no odd predecessor; at targets congruent to 5 modulo 9, its odd
predecessor is divisible by three and cannot belong to a positive cycle.
Starting backwards from the minimum forces factors 2, 4, 8, or 16 in the
cycle, according to the minimum's residue class.
-/
namespace Collatz.CycleInverseSpread
open AccCycle CycleExtremes

/-- An odd inverse branch is either absent or forbidden on a cycle in these
two target classes. Thus a predecessor not divisible by three must be twice v. -/
theorem forced_double {p v : Nat} (hp : acceleratedStep p=v) (hp3 : ¬3∣p)
    (hv : v%3=1 ∨ v%9=5) : p=2*v := by
  by_cases he : p%2=0
  · rw [acceleratedStep, if_pos he] at hp
    omega
  · rw [acceleratedStep, if_neg he] at hp
    rcases hv with hv | hv <;> omega

/-- Every attained cycle value has an attained predecessor which is not a
multiple of three. This is where the cycle hypothesis is essential. -/
theorem cycle_predecessor {m L v : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hv : ∃ i, acceleratedOrbit i m=v) :
    ∃ p, (∃ j, acceleratedOrbit j m=p) ∧ acceleratedStep p=v ∧ ¬3∣p := by
  obtain ⟨i, hi⟩ := hv
  refine ⟨acceleratedOrbit (i+L-1) m, ⟨i+L-1, rfl⟩, ?_, ?_⟩
  · rw [CycleMaxClass.accStep_pred h, hi]
  · exact CycleModThree.not_three_dvd_orbit hm h _

/-- At the minimum, an odd predecessor would be smaller than the minimum,
so the immediate predecessor must be exactly twice it. -/
theorem twice_min_attained {m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hmin : ∀ i, m≤acceleratedOrbit i m) :
    ∃ j, acceleratedOrbit j m=2*m := by
  obtain ⟨p, ⟨j, hj⟩, hp, _⟩ := cycle_predecessor (v := m) hm h ⟨0, rfl⟩
  have hlo : m≤p := by rw [← hj]; exact hmin j
  have heq : p=2*m := by
    by_cases he : p%2=0
    · rw [acceleratedStep, if_pos he] at hp
      omega
    · rw [acceleratedStep, if_neg he] at hp
      omega
  exact ⟨j, hj.trans heq⟩

/-- Lift an attained value through a forced doubling predecessor. -/
theorem double_attained {m L v : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hv : ∃ i, acceleratedOrbit i m=v) (hres : v%3=1 ∨ v%9=5) :
    ∃ j, acceleratedOrbit j m=2*v := by
  obtain ⟨p, ⟨j, hj⟩, hp, hp3⟩ := cycle_predecessor hm h hv
  exact ⟨j, hj.trans (forced_double hp hp3 hres)⟩

/-- A minimum congruent to 2 modulo 3 forces an attained value four times as large. -/
theorem four_min_attained {m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hmin : ∀ i, m≤acceleratedOrbit i m) (hres : m%3=2) :
    ∃ j, acceleratedOrbit j m=4*m := by
  have htwo := twice_min_attained hm h hmin
  have hfour := double_attained hm h htwo (Or.inl (by omega : (2*m)%3=1))
  simpa only [← Nat.mul_assoc] using hfour

/-- For a minimum 7 modulo 9, the odd predecessor of 2m is divisible by 3.
The next two inverse steps are forced, reaching 8m. -/
theorem eight_min_attained {m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hmin : ∀ i, m≤acceleratedOrbit i m) (hres : m%9=7) :
    ∃ j, acceleratedOrbit j m=8*m := by
  have htwo := twice_min_attained hm h hmin
  have hfour := double_attained hm h htwo (Or.inr (by omega : (2*m)%9=5))
  have hfour' : ∃ j, acceleratedOrbit j m=4*m := by
    simpa only [← Nat.mul_assoc] using hfour
  have height := double_attained hm h hfour' (Or.inl (by omega : (4*m)%3=1))
  simpa only [← Nat.mul_assoc] using height

/-- For a minimum 8 modulo 9, four consecutive inverse halvings are forced,
so the cycle contains 16m. -/
theorem sixteen_min_attained {m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hmin : ∀ i, m≤acceleratedOrbit i m) (hres : m%9=8) :
    ∃ j, acceleratedOrbit j m=16*m := by
  have hfour := four_min_attained hm h hmin (by omega)
  have height := double_attained hm h hfour (Or.inr (by omega : (4*m)%9=5))
  have height' : ∃ j, acceleratedOrbit j m=8*m := by
    simpa only [← Nat.mul_assoc] using height
  have hsixteen := double_attained hm h height' (Or.inl (by omega : (8*m)%3=1))
  simpa only [← Nat.mul_assoc] using hsixteen

/-- The attained inverse-chain endpoint supplies a lower bound on the maximum. -/
theorem attained_le_max {m L v : Nat} (h : AccIsCycleOf m L)
    (hv : ∃ j, acceleratedOrbit j m=v) : v≤cycleMax m L := by
  obtain ⟨j, hj⟩ := hv
  rw [← hj]
  exact le_cycleMax h j

/-- A compact residue-dependent lower factor for the cycle's spread. -/
def spreadFactor (m : Nat) : Nat :=
  if m%9=8 then 16 else if m%9=7 then 8 else if m%3=2 then 4 else 2

/-- The cycle maximum is at least the indicated multiple of its minimum.
This is a necessary condition, not a construction of a nontrivial cycle. -/
theorem residue_spread {m L : Nat} (hm : 0<m) (h : AccIsCycleOf m L)
    (hmin : ∀ i, m≤acceleratedOrbit i m) : spreadFactor m*m≤cycleMax m L := by
  unfold spreadFactor
  split
  · exact attained_le_max h (sixteen_min_attained hm h hmin ‹_›)
  · split
    · exact attained_le_max h (eight_min_attained hm h hmin ‹_›)
    · split
      · exact attained_le_max h (four_min_attained hm h hmin ‹_›)
      · exact attained_le_max h (twice_min_attained hm h hmin)

/-- The spread factor depends only on the minimum modulo nine. -/
theorem spreadFactor_mod_nine (m : Nat) : spreadFactor (m%9)=spreadFactor m := by
  simp only [spreadFactor, Nat.mod_mod, show m%9%3=m%3 from by omega]

/-- The six possible minimum classes modulo nine and their resulting factors. -/
theorem factor_table : spreadFactor 1=2 ∧ spreadFactor 2=4 ∧
    spreadFactor 4=2 ∧ spreadFactor 5=4 ∧ spreadFactor 7=8 ∧ spreadFactor 8=16 := by decide

/-- The excluded odd inverse branch is a real integer predecessor, illustrating
why the no-multiple-of-three condition cannot be omitted. -/
theorem forbidden_branch_example : acceleratedStep 9=14 ∧ 9≠2*14 ∧ 14%9=5 := by decide

end Collatz.CycleInverseSpread
