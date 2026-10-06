import Collatz.Strategy.FirstLightScan

/-!
# Reusable certificates for descent at a first coefficient crossing

The certificate has two parts: an arithmetic gap table, and first-crossing
checks below its exceptional-start threshold. Soundness quantifies over every
starting integer. A horizon bound on the first crossing remains a hypothesis.
-/

namespace Collatz.FirstLightCertificates
open FirstLightDescent AffineExact

/-- Generic certificate soundness: a finite gap bound plus a finite exceptional
range establishes first-crossing descent for unbounded starting values. -/
theorem descent_of_certificates (H N : Nat)
    (gap : ∀ k : Fin (H+1), ∀ a : Fin (k.val+1),
      3^a.val < 2^k.val → a.val*3^a.val < 3*(2^k.val-3^a.val)*N)
    (small : ∀ n : Fin N, 1<n.val →
      ∃ k : Fin (H+1), FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val)
    {n k : Nat} (hn : 1<n) (hk : k≤H) (hfirst : FirstLight n k) :
    acceleratedOrbit k n < n := by
  by_cases hsmall : n<N
  · obtain ⟨j, hj, hd⟩ := small ⟨n,hsmall⟩ hn
    have he := first_light_unique hj hfirst
    simpa only [he] using hd
  · have ha := oddCount_le_self n k
    have ht := gap ⟨k,by omega⟩ ⟨oddCount n k,by change oddCount n k < k+1; omega⟩ hfirst.1
    change oddCount n k * 3^oddCount n k <
      3*(2^k-3^oddCount n k)*N at ht
    by_cases hd : acceleratedOrbit k n < n
    · exact hd
    · have hb := failure_bound hfirst (by omega)
      have hm := Nat.mul_le_mul_left (3*(2^k-3^oddCount n k)) (show N≤n by omega)
      omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem gap_table_256 : ∀ k : Fin 257, ∀ a : Fin (k.val+1),
    3^a.val < 2^k.val → a.val*3^a.val < 3*(2^k.val-3^a.val)*6701 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem small_scan_6701 : FirstLightScan.checkRange 256 6701 = true := by
  decide

theorem small_starts_6701 : ∀ n : Fin 6701, 1<n.val →
    ∃ k : Fin 257, FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val :=
  FirstLightScan.checkRange_sound 256 6701 small_scan_6701

/-- All positive starts above 1 descend at their first coefficient crossing
if it occurs within 256 accelerated steps. The starting integer is unbounded. -/
theorem descent_at_first_light_le_256 {n k : Nat} (hn : 1<n)
    (hk : k≤256) (hfirst : FirstLight n k) : acceleratedOrbit k n < n :=
  descent_of_certificates 256 6701 gap_table_256 small_starts_6701 hn hk hfirst

end Collatz.FirstLightCertificates
