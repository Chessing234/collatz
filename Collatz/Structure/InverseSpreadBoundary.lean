import Collatz.Structure.CycleInverseSpread

/-!
# Exact stopping point of the elementary forced-doubling filter

At the endpoint from the residue table, an odd predecessor exists, is above
the proposed minimum, and is not divisible by three. Consequently these two
local filters cannot force one more doubling. This does not prove that the
odd predecessor lies on a cycle, or that the spread bounds are globally sharp.
-/
namespace Collatz.InverseSpreadBoundary
open CycleInverseSpread

/-- Targets in these two classes have an integral odd predecessor outside the
multiples of three, provided the target is even. -/
theorem admissible_odd_inverse {v : Nat} (he : v%2=0)
    (hr : v%9=2 ∨ v%9=8) :
    let p := (2*v-1)/3
    p%2=1 ∧ ¬3∣p ∧ 3*p+1=2*v ∧ acceleratedStep p=v := by
  have hp : ((2*v-1)/3)%2=1 := by rcases hr with hr | hr <;> omega
  have hp3 : ¬3∣(2*v-1)/3 := by rcases hr with hr | hr <;> omega
  have heq : 3*((2*v-1)/3)+1=2*v := by rcases hr with hr | hr <;> omega
  refine ⟨hp, hp3, heq, ?_⟩
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- The residue-table endpoint is even and has residue 2 or 8 modulo nine. -/
theorem endpoint_residue {m : Nat} (h3 : ¬3∣m) :
    (spreadFactor m*m)%2=0 ∧
    ((spreadFactor m*m)%9=2 ∨ (spreadFactor m*m)%9=8) := by
  unfold spreadFactor
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- Every residue-table factor is at least two. -/
theorem factor_ge_two (m : Nat) : 2≤spreadFactor m := by
  unfold spreadFactor
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- The endpoint always admits an odd predecessor that passes both elementary
cycle filters. No assertion of membership in an actual cycle is made. -/
theorem endpoint_has_admissible_odd {m : Nat} (h3 : ¬3∣m) :
    ∃ p, m≤p ∧ p%2=1 ∧ ¬3∣p ∧ acceleratedStep p=spreadFactor m*m ∧
      p<2*(spreadFactor m*m) := by
  let v := spreadFactor m*m
  have hr := endpoint_residue h3
  obtain ⟨hp, hp3, heq, ht⟩ := admissible_odd_inverse hr.1 hr.2
  have hv : 2*m≤v := Nat.mul_le_mul_right m (factor_ge_two m)
  refine ⟨(2*v-1)/3, ?_, hp, hp3, ht, ?_⟩ <;> dsimp [v] at * <;> omega

/-- The next inverse step is not forced to double by just minimality and the
exclusion of multiples of three. -/
theorem endpoint_not_forced {m : Nat} (h3 : ¬3∣m) :
    ¬(∀ p, m≤p → ¬3∣p → acceleratedStep p=spreadFactor m*m →
      p=2*(spreadFactor m*m)) := by
  obtain ⟨p, hp, _, hp3, ht, hlt⟩ := endpoint_has_admissible_odd h3
  intro hall
  have := hall p hp hp3 ht
  omega

/-- The competing even predecessor also passes the filters. -/
theorem endpoint_even_admissible {m : Nat} (h3 : ¬3∣m) :
    m≤2*(spreadFactor m*m) ∧ ¬3∣2*(spreadFactor m*m) ∧
    acceleratedStep (2*(spreadFactor m*m))=spreadFactor m*m := by
  have hr := endpoint_residue h3
  have hf := Nat.mul_le_mul_right m (factor_ge_two m)
  refine ⟨by omega, ?_, ?_⟩
  · rcases hr.2 with hr | hr <;> omega
  · simp [acceleratedStep]

/-- The endpoint has exactly these two inverse branches; both were shown
above to satisfy the local filters. -/
theorem endpoint_predecessors {m p : Nat} (h3 : ¬3∣m) :
    acceleratedStep p=spreadFactor m*m ↔
      p=2*(spreadFactor m*m) ∨ p=(2*(spreadFactor m*m)-1)/3 := by
  constructor
  · intro ht
    by_cases he : p%2=0
    · left
      rw [acceleratedStep, if_pos he] at ht
      omega
    · right
      rw [acceleratedStep, if_neg he] at ht
      omega
  · intro hp
    rcases hp with hp | hp
    · subst p
      exact (endpoint_even_admissible h3).2.2
    · subst p
      have hr := endpoint_residue h3
      exact (admissible_odd_inverse hr.1 hr.2).2.2.2

/-- A concrete branch point for proposed minimum 17: the forced chain ends
at 272, whose admissible predecessors are 544 and 181. -/
theorem endpoint_example : spreadFactor 17*17=272 ∧
    acceleratedStep 544=272 ∧ acceleratedStep 181=272 ∧
    17≤181 ∧ ¬3∣181 := by decide

end Collatz.InverseSpreadBoundary
