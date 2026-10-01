import Collatz.Structure.DensityLocalCounting

/-! Select a block-aligned parity modulus from any sufficiently large counting
cutoff. All bounds are integral, including the discarded-prefix scale. -/
namespace Collatz.GeneralPowerScaleSelection

/-- Every large cutoff has a block-aligned modulus in a fixed multiplicative
window, with an arbitrarily prescribed minimum block count. -/
theorem scale_exists (K D S N : Nat) (hK : 0<K) (hD : 0<D) (hN : D*2^(K*S)≤N) :
    ∃ s, S≤s ∧ D*2^(K*s)≤N ∧ N<D*2^K*2^(K*s) := by
  let v := N/D
  have hvbase : 2^(K*S)≤v := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa only [Nat.mul_comm] using hN
  have hvpos : 0<v := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hvbase
  let s := v.log2/K
  have hexplo : K*s≤v.log2 := by
    have := Nat.div_mul_le_self v.log2 K
    dsimp [s]
    simpa only [Nat.mul_comm] using this
  have hexphi : v.log2<K*(s+1) := by
    have := Nat.mod_lt v.log2 hK
    have := Nat.mod_add_div v.log2 K
    change v.log2%K+K*s=v.log2 at this
    rw [Nat.mul_succ]
    omega
  have hs : S≤s := by
    have hlog := (Nat.le_log2 (by omega : v≠0)).mpr hvbase
    apply (Nat.le_div_iff_mul_le hK).mpr
    simpa only [Nat.mul_comm] using hlog
  have hlo : 2^(K*s)≤v := (Nat.le_log2 (by omega : v≠0)).mp hexplo
  have hhi : v<2^(K*(s+1)) := (Nat.log2_lt (by omega : v≠0)).mp hexphi
  have hlow := Nat.mul_le_mul_left D hlo
  have hdiv : D*v≤N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N D
  have hupper : N<D*2^(K*(s+1)) := by
    have hm := Nat.mul_le_mul_left D (by omega : v+1≤2^(K*(s+1)))
    have hr := Nat.mod_lt N hD
    have he := Nat.mod_add_div N D
    change N%D+D*v=N at he
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  refine ⟨s, hs, Nat.le_trans hlow hdiv, ?_⟩
  simpa only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using hupper

end Collatz.GeneralPowerScaleSelection
