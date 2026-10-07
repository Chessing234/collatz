import Collatz.Strategy.FirstLightDescent

/-! Reduce a fixed-horizon gap certificate to its maximal light odd count.
This is scalar monotonicity, not a proof of crossing existence or priority. -/
namespace Collatz.Exploration.GapEndpointCertificates

/-- Checking the largest light odd count suffices for every smaller odd count. -/
theorem gap_of_endpoint {a A j N : Nat} (ha : a ≤ A)
    (hg : A*3^A < 3*(2^j-3^A)*N) :
    a*3^a < 3*(2^j-3^a)*N := by
  have hp : 3^a ≤ 3^A := Nat.pow_le_pow_right (by decide) ha
  have hm := Nat.mul_le_mul ha hp
  have hs : 2^j-3^A ≤ 2^j-3^a := by omega
  have hn := Nat.mul_le_mul_left 3 hs
  have ht := Nat.mul_le_mul_right N hn
  omega

/-- A single endpoint certificate rules out first-light failure below that odd-count cap. -/
theorem first_light_descent {n j A N : Nat}
    (hf : FirstLightDescent.FirstLight n j) (ha : oddCount n j ≤ A)
    (hn : N ≤ n) (hg : A*3^A < 3*(2^j-3^A)*N) :
    acceleratedOrbit j n < n := by
  by_cases hd : acceleratedOrbit j n < n
  · exact hd
  · have hb := FirstLightDescent.failure_bound hf (by omega)
    have hgap := gap_of_endpoint ha hg
    have hm := Nat.mul_le_mul_left (3*(2^j-3^oddCount n j)) hn
    omega

/-- A power bracket provides the maximal possible light odd count. -/
theorem odd_cap {a A j : Nat} (hl : 3^a < 2^j) (hc : 2^j ≤ 3^(A+1)) : a ≤ A := by
  by_cases ha : a ≤ A
  · exact ha
  · have hp : 3^(A+1) ≤ 3^a := Nat.pow_le_pow_right (by decide) (by omega)
    omega

def cap : Nat → Nat
  | 0 => 0
  | j+1 => if 3^(cap j+1) < 2^(j+1) then cap j+1 else cap j

/-- The computable cap always brackets the horizon's coefficient threshold from above. -/
theorem cap_bracket (j : Nat) : 2^j ≤ 3^(cap j+1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [cap]
    split
    · have hm := Nat.mul_le_mul_right 2 ih
      have he : 3^(cap j+1)*2 ≤ 3^(cap j+1)*3 :=
        Nat.mul_le_mul_left _ (by decide)
      rw [Nat.pow_succ,Nat.pow_succ]
      exact Nat.le_trans hm he
    · omega

/-- A light orbit prefix's odd count lies below the computed endpoint. -/
theorem light_oddCount_cap {n j : Nat} (hl : 3^oddCount n j < 2^j) :
    oddCount n j ≤ cap j := odd_cap hl (cap_bracket j)

/-- A verified endpoint test implies first-light descent for all sources above N. -/
theorem descent_of_endpoint {n j N : Nat}
    (hf : FirstLightDescent.FirstLight n j) (hn : N ≤ n)
    (hg : cap j*3^cap j < 3*(2^j-3^cap j)*N) :
    acceleratedOrbit j n < n :=
  first_light_descent hf (light_oddCount_cap hf.1) hn hg

end Collatz.Exploration.GapEndpointCertificates
