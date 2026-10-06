import Collatz.Structure.DensityLocalCounting

/-! Select a block-aligned parity modulus from any sufficiently large counting
cutoff. All bounds are integral, including the discarded-prefix scale. -/
namespace Collatz.PowerScaleSelection

/-- Every large cutoff has a 125-step-aligned modulus in a fixed multiplicative
window, with an arbitrarily prescribed minimum block count. -/
theorem scale_exists (D S N : Nat) (hD : 0<D) (hN : D*2^(125*S)≤N) :
    ∃ s, S≤s ∧ D*2^(125*s)≤N ∧ N<D*2^125*2^(125*s) := by
  let v := N/D
  have hvbase : 2^(125*S)≤v := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa only [Nat.mul_comm] using hN
  have hvpos : 0<v := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hvbase
  let s := v.log2/125
  have hexplo : 125*s≤v.log2 := by
    have := Nat.div_mul_le_self v.log2 125
    dsimp [s]
    omega
  have hexphi : v.log2<125*(s+1) := by
    have := Nat.mod_lt v.log2 (by decide : 0<125)
    have := Nat.mod_add_div v.log2 125
    dsimp [s]
    omega
  have hs : S≤s := by
    have hlog := (Nat.le_log2 (by omega : v≠0)).mpr hvbase
    dsimp [s]
    omega
  have hlo : 2^(125*s)≤v := (Nat.le_log2 (by omega : v≠0)).mp hexplo
  have hhi : v<2^(125*(s+1)) := (Nat.log2_lt (by omega : v≠0)).mp hexphi
  have hlow := Nat.mul_le_mul_left D hlo
  have hdiv : D*v≤N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N D
  have hupper : N<D*2^(125*(s+1)) := by
    have hm := Nat.mul_le_mul_left D (by omega : v+1≤2^(125*(s+1)))
    have hr := Nat.mod_lt N hD
    have he := Nat.mod_add_div N D
    change N%D+D*v=N at he
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  refine ⟨s, hs, Nat.le_trans hlow hdiv, ?_⟩
  simpa only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using hupper

end Collatz.PowerScaleSelection
