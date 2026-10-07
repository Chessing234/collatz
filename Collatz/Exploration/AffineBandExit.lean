import Collatz.Exploration.FloorAffineError

/-! Necessary coefficient-spread conditions for two endpoints to remain in a band.
These are conditional finite-prefix results, not universal exit certificates. -/
namespace Collatz.Exploration.AffineBandExit
open FloorAffineError

/-- Eliminate the source between a low affine endpoint and a high endpoint. -/
theorem spread_budget {D L E H n x y B b P Q g : Nat}
    (hx : D*x = L*n+B) (hy : H*n ≤ E*y)
    (hf : b ≤ x) (hu : Q*y ≤ P*b)
    (hg : P*L*E+g ≤ Q*H*D) : g*b ≤ Q*H*B := by
  have h1 := Nat.mul_le_mul_left (Q*H*D) hf
  have h2 := Nat.mul_le_mul_left (Q*L) hy
  have h3 := Nat.mul_le_mul_left (L*E) hu
  have h4 := Nat.mul_le_mul_right b hg
  have he := congrArg (fun z => Q*H*z) hx
  simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm] at h1 h2 h3 h4 he ⊢
  omega

/-- Survival plus a coefficient gap forces a floor-dependent budget inequality. -/
theorem floor_spread_budget {n b a c B P Q g : Nat}
    (hb : 0 < b)
    (hf : ∀ i, i < a → b ≤ acceleratedOrbit i n)
    (he : 2^a*acceleratedOrbit a n = 3^oddCount n a*n+B)
    (hl : b ≤ acceleratedOrbit a n)
    (hu : Q*acceleratedOrbit c n ≤ P*b)
    (hn : Q*n ≤ P*b)
    (hh : 3^oddCount n c*n ≤ 2^c*acceleratedOrbit c n)
    (hg : P*3^oddCount n a*2^c+g ≤ Q*3^oddCount n c*2^a) :
    g*(weight b-oddCount n a) ≤
      P*3^oddCount n c*oddCount n a*3^oddCount n a := by
  have hs := spread_budget he hh hl hu hg
  have hp := survival_offset_paid hf he
  have h1 := Nat.mul_le_mul_right (weight b-oddCount n a) hs
  have h2 := Nat.mul_le_mul_left (Q*3^oddCount n c) hp
  have h3 := Nat.mul_le_mul_left
    (3^oddCount n c*oddCount n a*3^oddCount n a) hn
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at h1 h2 h3
  have hbound :
      (g*(weight b-oddCount n a))*b ≤
      (P*3^oddCount n c*oddCount n a*3^oddCount n a)*b := by
    simp only [Nat.mul_left_comm, Nat.mul_comm]
    omega
  exact Nat.le_of_mul_le_mul_right hbound hb

end Collatz.Exploration.AffineBandExit
