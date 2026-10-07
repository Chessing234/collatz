import Collatz.Exploration.FloorProductError

/-! A limitation of product spread certificates, not a claim of band survival. -/
namespace Collatz.Exploration.ProductSpreadObstruction
open FloorAffineError FloorProductError

/-- A coefficient pair already inside the target width cannot trigger strict product spread. -/
theorem no_strict_spread {L H D E P Q b k : Nat}
    (hc : Q*H*D ≤ P*E*L) :
    Q*H*D*base b^k ≤ P*E*L*weight b^k := by
  have hw : base b ≤ weight b := by unfold base weight; omega
  exact Nat.mul_le_mul hc (Nat.pow_le_pow_left hw k)

/-- A coefficient corridor [1,R] prevents strict width-R spread for every floor. -/
theorem corridor_obstruction {L H D E R b k : Nat}
    (hl : D ≤ L) (hh : H ≤ R*E) :
    H*D*base b^k ≤ R*E*L*weight b^k := by
  have hc : H*D ≤ R*E*L := by
    have h1 := Nat.mul_le_mul_right D hh
    have h2 := Nat.mul_le_mul_left (R*E) hl
    exact Nat.le_trans h1 h2
  have hz := no_strict_spread (Q := 1) (P := R) (b := b) (k := k) (by simpa using hc)
  simpa using hz

/-- Apply the limitation to the actual odd-count coefficients of an orbit. -/
theorem orbit_corridor_obstruction {n a c R b : Nat}
    (hl : 2^a ≤ 3^oddCount n a)
    (hh : 3^oddCount n c ≤ R*2^c) :
    ¬ (R*2^c*3^oddCount n a*weight b^oddCount n a <
      3^oddCount n c*2^a*base b^oddCount n a) := by
  have h := corridor_obstruction (b := b) (k := oddCount n a) hl hh
  omega

end Collatz.Exploration.ProductSpreadObstruction
