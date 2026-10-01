import Collatz.Strategy.FirstLightConsequences

/-!
# Exact finite-horizon residue classification

Odd counts up to H depend only on the starting residue modulo 2^H.
Whenever first-crossing descent is certified through H, this classifies the
actual no-descent prefixes of every starting value greater than 1, not only
sufficiently large representatives. The exclusions 0 and 1 are essential.
-/
namespace Collatz.FirstLightPeriodicity
open FirstLightDescent FirstLightConsequences

/-- Agreement at a high binary modulus determines every shorter odd-count prefix. -/
theorem oddCount_congr {n m H j : Nat} (hj : j≤H)
    (hmod : n%2^H = m%2^H) : oddCount n j = oddCount m j := by
  have hlow := congrArg (fun r => r%2^j) hmod
  rw [Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 hj),
    Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 hj)] at hlow
  rw [Density.oddCount_mod n j, Density.oddCount_mod m j, hlow]

/-- First-crossing predicates transport across the high residue class. -/
theorem firstLight_transport {n m H k : Nat} (hk : k≤H)
    (hmod : n%2^H = m%2^H) (hf : FirstLight n k) : FirstLight m k := by
  constructor
  · simpa only [oddCount_congr hk hmod] using hf.1
  · intro j hj
    simpa only [oddCount_congr (by omega : j≤H) hmod] using hf.2 j hj

/-- The exact crossing index through H is constant on binary residue classes. -/
theorem firstLight_congr {n m H k : Nat} (hk : k≤H)
    (hmod : n%2^H = m%2^H) : FirstLight n k ↔ FirstLight m k :=
  ⟨firstLight_transport hk hmod, firstLight_transport hk hmod.symm⟩

/-- With a certificate, the same is true of the first actual descent index. -/
theorem firstDescent_congr {n m H k : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hm : 1<m) (hk : k≤H) (hmod : n%2^H = m%2^H) :
    FirstDescent n k ↔ FirstDescent m k := by
  rw [first_descent_iff_first_light hc hn hk, first_descent_iff_first_light hc hm hk]
  exact firstLight_congr hk hmod

/-- The whole no-descent window has exact residue dependence above 1. -/
theorem noDescent_congr {n m H : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hm : 1<m) (hmod : n%2^H = m%2^H) :
    (∀ j, j≤H → n≤acceleratedOrbit j n) ↔
      (∀ j, j≤H → m≤acceleratedOrbit j m) := by
  rw [no_descent_iff_heavy_prefix hc hn, no_descent_iff_heavy_prefix hc hm]
  constructor
  · intro h j hj
    simpa only [oddCount_congr hj hmod] using h j hj
  · intro h j hj
    simpa only [oddCount_congr hj hmod.symm] using h j hj

/-- Periodicity of actual finite-horizon survival, away from the two base inputs. -/
theorem noDescent_add_period {n H : Nat} (hc : ExactThrough H) (hn : 1<n) :
    (∀ j, j≤H → n≤acceleratedOrbit j n) ↔
      (∀ j, j≤H → n+2^H≤acceleratedOrbit j (n+2^H)) := by
  apply noDescent_congr (m := n+2^H) hc hn (Nat.lt_of_lt_of_le hn (Nat.le_add_right n (2^H)))
  simp

/-- The checked 256-step horizon yields an unconditional periodic classification. -/
theorem noDescent_256_congr {n m : Nat} (hn : 1<n) (hm : 1<m)
    (hmod : n%2^256 = m%2^256) :
    (∀ j, j≤256 → n≤acceleratedOrbit j n) ↔
      (∀ j, j≤256 → m≤acceleratedOrbit j m) :=
  noDescent_congr exactThrough_256 hn hm hmod

end Collatz.FirstLightPeriodicity
