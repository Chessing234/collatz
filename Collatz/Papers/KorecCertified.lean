import Collatz.Structure.PowerDensityParameters
import Collatz.Structure.GeneralPowerScaleSelection
import Collatz.Structure.PowerTailCounting

/-! A uniform density proof from a finite integer certificate. The certificate
contains only strict moment and multiplier gaps, not a density hypothesis. -/
namespace Collatz.Papers.Korec1994
open NaturalDensity ParityMoments PowerDensityParameters

/-- Arbitrary reciprocal precision for the high-odd-count tail of a certificate. -/
theorem certified_tail_precision {p q : Nat} (c : Certificate p q) (r s : Nat)
    (hs : r*(c.oddWeight+c.evenWeight)^c.block≤s) :
    r*tailCount (c.block*s) (c.threshold*s)<2^(c.block*s) := by
  have hg := GeometricPrecision.scaled_power_lt
    ((c.oddWeight+c.evenWeight)^c.block)
    (2^c.block*(c.oddWeight^c.threshold*c.evenWeight^(c.block-c.threshold))) r s
    (Nat.pow_pos c.weights_pos) c.moment_gap hs
  have ht := tail_moment_bound c.oddWeight c.evenWeight
    (c.block*s) (c.threshold*s) c.weights_order
  have ht' : (c.oddWeight^c.threshold*c.evenWeight^(c.block-c.threshold))^s *
      tailCount (c.block*s) (c.threshold*s)≤((c.oddWeight+c.evenWeight)^c.block)^s := by
    simpa only [weight, ← Nat.sub_mul, Nat.pow_mul, Nat.mul_pow] using ht
  have hc := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left r ht') hg
  have he : (c.oddWeight^c.threshold*c.evenWeight^(c.block-c.threshold))^s *
      (r*tailCount (c.block*s) (c.threshold*s)) <
      (c.oddWeight^c.threshold*c.evenWeight^(c.block-c.threshold))^s*2^(c.block*s) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hc
  exact Nat.lt_of_mul_lt_mul_left he

/-- Absorb an arbitrary affine prefactor using the certificate's multiplier gap. -/
theorem certified_multiplier_precision {p q : Nat} (c : Certificate p q) (L s : Nat)
    (hs : (L+1)^q*3^(q*c.threshold)≤s) :
    ((L+1)*3^(c.threshold*s))^q < (2^(c.block*s))^p := by
  have h := GeometricPrecision.scaled_power_lt (3^(q*c.threshold)) (2^(p*c.block))
    ((L+1)^q) s (Nat.pow_pos (by decide)) c.multiplier_gap hs
  simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

/-- A certified parity threshold guarantees the actual strict power target
throughout a sufficiently large multiplicative scale interval. -/
theorem certified_endpoint_power {p q n L s : Nat} (c : Certificate p q)
    (hs : (L+1)^q*3^(q*c.threshold)≤s)
    (hnlo : 2^(c.block*s)≤n) (hnhi : n≤L*2^(c.block*s))
    (ha : oddCount n (c.block*s)≤c.threshold*s) :
    (acceleratedOrbit (c.block*s) n)^q<n^p := by
  have hu := PowerOrbitScale.orbit_upper hnhi
  have hp := Nat.mul_le_mul_left (L+1)
    (Nat.pow_le_pow_right (by decide : 1≤(3:Nat)) ha)
  have hsmall := Nat.pow_le_pow_left (Nat.le_trans hu hp) q
  have hlarge := Nat.pow_le_pow_left hnlo p
  exact Nat.lt_of_le_of_lt hsmall
    (Nat.lt_of_lt_of_le (certified_multiplier_precision c L s hs) hlarge)

/-- The certified endpoint also supplies the unbounded existential predicate. -/
theorem certified_power_on_scale {p q n L s : Nat} (c : Certificate p q)
    (hs : (L+1)^q*3^(q*c.threshold)≤s)
    (hnlo : 2^(c.block*s)≤n) (hnhi : n≤L*2^(c.block*s))
    (ha : oddCount n (c.block*s)≤c.threshold*s) : OrbitBelowPower p q n :=
  ⟨c.block*s, certified_endpoint_power c hs hnlo hnhi ha⟩

/-- Transfer any property supplied on the light part of the selected scale,
retaining the same prefix and periodic-tail bounds. -/
theorem certified_property_failure_count {p q : Nat} (c : Certificate p q)
    (P : Nat → Prop) (L s N : Nat) (hN : N≤L*2^(c.block*s))
    (hcover : ∀ n, 2^(c.block*s)≤n → n≤L*2^(c.block*s) →
      oddCount n (c.block*s)≤c.threshold*s → P n) :
    predicateCount (fun n => ¬P n) N ≤
      2^(c.block*s)+(N/2^(c.block*s)+1)*tailCount (c.block*s) (c.threshold*s) := by
  have hi := predicateCount_local_mono (fun n => ¬P n)
    (fun n => c.threshold*s≤oddCount n (c.block*s)) (2^(c.block*s)) N (by
      intro n hn hlo hf
      by_cases ha : oddCount n (c.block*s)≤c.threshold*s
      · exact False.elim (hf (hcover n hn (by omega) ha))
      · omega)
  exact Nat.le_trans hi (Nat.add_le_add_left
    (PowerTailCounting.tail_count_upper (c.block*s) (c.threshold*s) N) _)

/-- Count actual power failures by a prefix and a periodic parity tail. -/
theorem certified_failure_count {p q : Nat} (c : Certificate p q) (L s N : Nat)
    (hs : (L+1)^q*3^(q*c.threshold)≤s) (hN : N≤L*2^(c.block*s)) :
    predicateCount (fun n => ¬OrbitBelowPower p q n) N ≤
      2^(c.block*s)+(N/2^(c.block*s)+1)*tailCount (c.block*s) (c.threshold*s) :=
  certified_property_failure_count c (OrbitBelowPower p q) L s N hN
    (fun _ hlo hhi ha => certified_power_on_scale c hs hlo hhi ha)

/-- Uniform precision for any property eventually supplied by the certified
light scales. This exposes the common counting argument for refinements. -/
theorem certified_property_failure_precision {p q : Nat} (c : Certificate p q)
    (P : Nat → Prop)
    (hcover : ∀ L, ∃ S, ∀ s, S≤s → ∀ n, 2^(c.block*s)≤n → n≤L*2^(c.block*s) →
      oddCount n (c.block*s)≤c.threshold*s → P n)
    (r : Nat) (hr : 0<r) :
    ∃ N0, ∀ N, N0≤N → r*predicateCount (fun n => ¬P n) N≤N := by
  let D := 2*r
  let L := D*2^c.block
  obtain ⟨SP, hSP⟩ := hcover L
  let S := max ((4*r)*(c.oddWeight+c.evenWeight)^c.block) SP
  refine ⟨D*2^(c.block*S), ?_⟩
  intro N hN
  obtain ⟨s, hs, hprefix, hscale⟩ := GeneralPowerScaleSelection.scale_exists
    c.block D S N c.block_pos (by dsimp [D]; omega) hN
  have htail := Nat.le_of_lt (certified_tail_precision c (4*r) s
    (Nat.le_trans (Nat.le_max_left _ _) hs))
  have hcount := certified_property_failure_count c P L s N (Nat.le_of_lt hscale)
    (hSP s (Nat.le_trans (Nat.le_max_right _ _) hs))
  exact prefix_and_period_precision r (2^(c.block*s)) N
    (tailCount (c.block*s) (c.threshold*s))
    (predicateCount (fun n => ¬P n) N) hr hprefix htail hcount

/-- Abstract density conclusion for a property of the certified light scales. -/
theorem density_one_of_scale_property {p q : Nat} (c : Certificate p q)
    (P : Nat → Prop)
    (hcover : ∀ L, ∃ S, ∀ s, S≤s → ∀ n, 2^(c.block*s)≤n → n≤L*2^(c.block*s) →
      oddCount n (c.block*s)≤c.threshold*s → P n) : DensityOne P :=
  densityOne_of_complement_precision (certified_property_failure_precision c P hcover)

/-- Every certificate gives explicit all-cutoff upper bounds on power failures. -/
theorem certified_failure_precision {p q : Nat} (c : Certificate p q)
    (r : Nat) (hr : 0<r) :
    ∃ N0, ∀ N, N0≤N → r*predicateCount (fun n => ¬OrbitBelowPower p q n) N≤N := by
  apply certified_property_failure_precision c (OrbitBelowPower p q) _ r hr
  intro L
  exact ⟨(L+1)^q*3^(q*c.threshold), fun _ hs _ hlo hhi ha =>
    certified_power_on_scale c hs hlo hhi ha⟩

/-- Density one follows from the integer certificate, without any assumption
of universal convergence or of the published theorem. -/
theorem density_one_of_certificate {p q : Nat} (c : Certificate p q) :
    DensityOne (OrbitBelowPower p q) :=
  densityOne_of_complement_precision (certified_failure_precision c)

/-- The full recorded rational-exponent statement of Korec's theorem. -/
theorem rationalExponentStatement_proved : rationalExponentStatement := by
  intro p q _ hgap
  obtain ⟨c⟩ := certificate_exists p q hgap
  exact density_one_of_certificate c

end Collatz.Papers.Korec1994
