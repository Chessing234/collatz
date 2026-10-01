import Collatz.Strategy.FirstLightCertificates
import Collatz.Strategy.AffineObstruction

/-!
# Stopping-time consequences of a first-crossing certificate

A certificate through horizon H proves more than descent at a special index:
within that horizon the first descent and first coefficient crossing coincide,
and the no-descent prefixes are exactly the heavy prefixes. H is finite and
the starting value is unbounded. No existence beyond the horizon is asserted.
-/
namespace Collatz.FirstLightConsequences
open FirstLightDescent

/-- The first index at which the actual accelerated orbit goes below its start. -/
def FirstDescent (n k : Nat) : Prop :=
  acceleratedOrbit k n < n ∧ ∀ j, j<k → n ≤ acceleratedOrbit j n

/-- The property supplied by a checked finite-horizon crossing certificate. -/
def ExactThrough (H : Nat) : Prop :=
  ∀ n k, 1<n → k≤H → FirstLight n k → acceleratedOrbit k n < n

/-- Any light prefix has a least light prefix no later than itself. -/
theorem exists_first_light (n k : Nat) (hl : 3^oddCount n k < 2^k) :
    ∃ j, j≤k ∧ FirstLight n j := by
  classical
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hex : ∃ j, j<k ∧ 3^oddCount n j < 2^j
    · obtain ⟨j, hj, hlight⟩ := hex
      obtain ⟨i, hi, hf⟩ := ih j hj hlight
      exact ⟨i, by omega, hf⟩
    · refine ⟨k, Nat.le_refl k, hl, ?_⟩
      intro j hj
      have hnot : ¬ 3^oddCount n j < 2^j := fun h => hex ⟨j, hj, h⟩
      omega

/-- No actual descent can occur before a first coefficient crossing. -/
theorem no_descent_before_first_light {n k : Nat} (hf : FirstLight n k) :
    ∀ j, j<k → n ≤ acceleratedOrbit j n := by
  intro j hj
  have hp := hf.2 j hj
  by_cases hd : acceleratedOrbit j n < n
  · have := AffineObstruction.light_of_drop hd
    omega
  · omega

/-- Under the certificate, a first crossing is exactly a first actual descent. -/
theorem first_light_is_first_descent {H n k : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hk : k≤H) (hf : FirstLight n k) : FirstDescent n k :=
  ⟨hc n k hn hk hf, no_descent_before_first_light hf⟩

/-- A light prefix inside the horizon guarantees an actual descent by that index. -/
theorem descent_by_light_prefix {H n k : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hk : k≤H) (hl : 3^oddCount n k < 2^k) :
    ∃ j, j≤k ∧ acceleratedOrbit j n < n := by
  obtain ⟨j, hj, hf⟩ := exists_first_light n k hl
  exact ⟨j, hj, hc n j hn (by omega) hf⟩

/-- Conversely, a first actual descent inside the horizon is a first crossing. -/
theorem first_descent_is_first_light {H n k : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hk : k≤H) (hd : FirstDescent n k) : FirstLight n k := by
  refine ⟨AffineObstruction.light_of_drop hd.1, ?_⟩
  intro j hj
  by_cases hl : 3^oddCount n j < 2^j
  · obtain ⟨i, hi, hdrop⟩ := descent_by_light_prefix hc hn (by omega : j≤H) hl
    have := hd.2 i (by omega)
    omega
  · omega

/-- Exact finite-horizon equality of the two first-event predicates. -/
theorem first_descent_iff_first_light {H n k : Nat} (hc : ExactThrough H)
    (hn : 1<n) (hk : k≤H) : FirstDescent n k ↔ FirstLight n k :=
  ⟨first_descent_is_first_light hc hn hk, first_light_is_first_descent hc hn hk⟩

/-- Within the certified horizon, no-descent prefixes and heavy prefixes agree. -/
theorem no_descent_iff_heavy_prefix {H n : Nat} (hc : ExactThrough H) (hn : 1<n) :
    (∀ j, j≤H → n ≤ acceleratedOrbit j n) ↔
      (∀ j, j≤H → 2^j ≤ 3^oddCount n j) := by
  constructor
  · intro h j hj
    by_cases hl : 3^oddCount n j < 2^j
    · obtain ⟨i, hi, hd⟩ := descent_by_light_prefix hc hn hj hl
      have := h i (by omega)
      omega
    · omega
  · intro h j hj
    by_cases hd : acceleratedOrbit j n < n
    · have := AffineObstruction.light_of_drop hd
      have := h j hj
      omega
    · omega

/-- Certificates restrict to every shorter horizon. -/
theorem exactThrough_mono {H K : Nat} (hc : ExactThrough H) (hKH : K≤H) :
    ExactThrough K := fun n k hn hk hf => hc n k hn (by omega) hf

/-- The previously checked 256-step certificate supplies all these consequences. -/
theorem exactThrough_256 : ExactThrough 256 :=
  fun _ _ hn hk hf => FirstLightCertificates.descent_at_first_light_le_256 hn hk hf

end Collatz.FirstLightConsequences
