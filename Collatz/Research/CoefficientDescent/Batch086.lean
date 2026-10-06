import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch086

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5695. -/
theorem certificate_5695 : classCertificateB 10 5695 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5695 (m : Nat) : stoppingTime (2 ^ 10 * m + 5695) 10 :=
  stoppingTime_of_classCertificate certificate_5695 m

/-- Checked base and every prefix for input 5697. -/
theorem certificate_5697 : classCertificateB 2 5697 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5697 (m : Nat) : stoppingTime (2 ^ 2 * m + 5697) 2 :=
  stoppingTime_of_classCertificate certificate_5697 m

/-- Checked base and every prefix for input 5699. -/
theorem certificate_5699 : classCertificateB 4 5699 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5699 (m : Nat) : stoppingTime (2 ^ 4 * m + 5699) 4 :=
  stoppingTime_of_classCertificate certificate_5699 m

/-- Checked base and every prefix for input 5701. -/
theorem certificate_5701 : classCertificateB 2 5701 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5701 (m : Nat) : stoppingTime (2 ^ 2 * m + 5701) 2 :=
  stoppingTime_of_classCertificate certificate_5701 m

/-- Checked base and every prefix for input 5703. -/
theorem certificate_5703 : classCertificateB 10 5703 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5703 (m : Nat) : stoppingTime (2 ^ 10 * m + 5703) 10 :=
  stoppingTime_of_classCertificate certificate_5703 m

/-- Checked base and every prefix for input 5705. -/
theorem certificate_5705 : classCertificateB 2 5705 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5705 (m : Nat) : stoppingTime (2 ^ 2 * m + 5705) 2 :=
  stoppingTime_of_classCertificate certificate_5705 m

/-- Checked base and every prefix for input 5707. -/
theorem certificate_5707 : classCertificateB 5 5707 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5707 (m : Nat) : stoppingTime (2 ^ 5 * m + 5707) 5 :=
  stoppingTime_of_classCertificate certificate_5707 m

/-- Checked base and every prefix for input 5709. -/
theorem certificate_5709 : classCertificateB 2 5709 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5709 (m : Nat) : stoppingTime (2 ^ 2 * m + 5709) 2 :=
  stoppingTime_of_classCertificate certificate_5709 m

/-- Checked base and every prefix for input 5711. -/
theorem certificate_5711 : classCertificateB 8 5711 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5711 (m : Nat) : stoppingTime (2 ^ 8 * m + 5711) 8 :=
  stoppingTime_of_classCertificate certificate_5711 m

/-- Checked base and every prefix for input 5713. -/
theorem certificate_5713 : classCertificateB 2 5713 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5713 (m : Nat) : stoppingTime (2 ^ 2 * m + 5713) 2 :=
  stoppingTime_of_classCertificate certificate_5713 m

/-- Checked base and every prefix for input 5715. -/
theorem certificate_5715 : classCertificateB 4 5715 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5715 (m : Nat) : stoppingTime (2 ^ 4 * m + 5715) 4 :=
  stoppingTime_of_classCertificate certificate_5715 m

/-- Checked base and every prefix for input 5717. -/
theorem certificate_5717 : classCertificateB 2 5717 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5717 (m : Nat) : stoppingTime (2 ^ 2 * m + 5717) 2 :=
  stoppingTime_of_classCertificate certificate_5717 m

/-- Checked base and every prefix for input 5719. -/
theorem certificate_5719 : classCertificateB 5 5719 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5719 (m : Nat) : stoppingTime (2 ^ 5 * m + 5719) 5 :=
  stoppingTime_of_classCertificate certificate_5719 m

/-- Checked base and every prefix for input 5721. -/
theorem certificate_5721 : classCertificateB 2 5721 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5721 (m : Nat) : stoppingTime (2 ^ 2 * m + 5721) 2 :=
  stoppingTime_of_classCertificate certificate_5721 m

/-- Checked base and every prefix for input 5723. -/
theorem certificate_5723 : classCertificateB 13 5723 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5723 (m : Nat) : stoppingTime (2 ^ 13 * m + 5723) 13 :=
  stoppingTime_of_classCertificate certificate_5723 m

/-- Checked base and every prefix for input 5725. -/
theorem certificate_5725 : classCertificateB 2 5725 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5725 (m : Nat) : stoppingTime (2 ^ 2 * m + 5725) 2 :=
  stoppingTime_of_classCertificate certificate_5725 m

/-- Checked base and every prefix for input 5727. -/
theorem certificate_5727 : classCertificateB 8 5727 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5727 (m : Nat) : stoppingTime (2 ^ 8 * m + 5727) 8 :=
  stoppingTime_of_classCertificate certificate_5727 m

/-- Checked base and every prefix for input 5729. -/
theorem certificate_5729 : classCertificateB 2 5729 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5729 (m : Nat) : stoppingTime (2 ^ 2 * m + 5729) 2 :=
  stoppingTime_of_classCertificate certificate_5729 m

/-- Checked base and every prefix for input 5731. -/
theorem certificate_5731 : classCertificateB 4 5731 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5731 (m : Nat) : stoppingTime (2 ^ 4 * m + 5731) 4 :=
  stoppingTime_of_classCertificate certificate_5731 m

/-- Checked base and every prefix for input 5733. -/
theorem certificate_5733 : classCertificateB 2 5733 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5733 (m : Nat) : stoppingTime (2 ^ 2 * m + 5733) 2 :=
  stoppingTime_of_classCertificate certificate_5733 m

/-- Checked base and every prefix for input 5735. -/
theorem certificate_5735 : classCertificateB 24 5735 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5735 (m : Nat) : stoppingTime (2 ^ 24 * m + 5735) 24 :=
  stoppingTime_of_classCertificate certificate_5735 m

/-- Checked base and every prefix for input 5737. -/
theorem certificate_5737 : classCertificateB 2 5737 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5737 (m : Nat) : stoppingTime (2 ^ 2 * m + 5737) 2 :=
  stoppingTime_of_classCertificate certificate_5737 m

/-- Checked base and every prefix for input 5739. -/
theorem certificate_5739 : classCertificateB 5 5739 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5739 (m : Nat) : stoppingTime (2 ^ 5 * m + 5739) 5 :=
  stoppingTime_of_classCertificate certificate_5739 m

/-- Checked base and every prefix for input 5741. -/
theorem certificate_5741 : classCertificateB 2 5741 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5741 (m : Nat) : stoppingTime (2 ^ 2 * m + 5741) 2 :=
  stoppingTime_of_classCertificate certificate_5741 m

/-- Checked base and every prefix for input 5743. -/
theorem certificate_5743 : classCertificateB 12 5743 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5743 (m : Nat) : stoppingTime (2 ^ 12 * m + 5743) 12 :=
  stoppingTime_of_classCertificate certificate_5743 m

/-- Checked base and every prefix for input 5745. -/
theorem certificate_5745 : classCertificateB 2 5745 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5745 (m : Nat) : stoppingTime (2 ^ 2 * m + 5745) 2 :=
  stoppingTime_of_classCertificate certificate_5745 m

/-- Checked base and every prefix for input 5747. -/
theorem certificate_5747 : classCertificateB 4 5747 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5747 (m : Nat) : stoppingTime (2 ^ 4 * m + 5747) 4 :=
  stoppingTime_of_classCertificate certificate_5747 m

/-- Checked base and every prefix for input 5749. -/
theorem certificate_5749 : classCertificateB 2 5749 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5749 (m : Nat) : stoppingTime (2 ^ 2 * m + 5749) 2 :=
  stoppingTime_of_classCertificate certificate_5749 m

/-- Checked base and every prefix for input 5751. -/
theorem certificate_5751 : classCertificateB 5 5751 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5751 (m : Nat) : stoppingTime (2 ^ 5 * m + 5751) 5 :=
  stoppingTime_of_classCertificate certificate_5751 m

/-- Checked base and every prefix for input 5753. -/
theorem certificate_5753 : classCertificateB 2 5753 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5753 (m : Nat) : stoppingTime (2 ^ 2 * m + 5753) 2 :=
  stoppingTime_of_classCertificate certificate_5753 m

/-- Checked base and every prefix for input 5755. -/
theorem certificate_5755 : classCertificateB 8 5755 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5755 (m : Nat) : stoppingTime (2 ^ 8 * m + 5755) 8 :=
  stoppingTime_of_classCertificate certificate_5755 m

/-- Checked base and every prefix for input 5757. -/
theorem certificate_5757 : classCertificateB 2 5757 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5757 (m : Nat) : stoppingTime (2 ^ 2 * m + 5757) 2 :=
  stoppingTime_of_classCertificate certificate_5757 m

/-- Checked base and every prefix for input 5759. -/
theorem certificate_5759 : classCertificateB 35 5759 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5759 (m : Nat) : stoppingTime (2 ^ 35 * m + 5759) 35 :=
  stoppingTime_of_classCertificate certificate_5759 m

/-- Checked base and every prefix for input 5761. -/
theorem certificate_5761 : classCertificateB 2 5761 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5761 (m : Nat) : stoppingTime (2 ^ 2 * m + 5761) 2 :=
  stoppingTime_of_classCertificate certificate_5761 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5695 5763 := by
  intro n hlo hhi hodd
  have hn : n = 5695 ∨ n = 5697 ∨ n = 5699 ∨ n = 5701 ∨ n = 5703 ∨ n = 5705 ∨ n = 5707 ∨ n = 5709 ∨ n = 5711 ∨ n = 5713 ∨ n = 5715 ∨ n = 5717 ∨ n = 5719 ∨ n = 5721 ∨ n = 5723 ∨ n = 5725 ∨ n = 5727 ∨ n = 5729 ∨ n = 5731 ∨ n = 5733 ∨ n = 5735 ∨ n = 5737 ∨ n = 5739 ∨ n = 5741 ∨ n = 5743 ∨ n = 5745 ∨ n = 5747 ∨ n = 5749 ∨ n = 5751 ∨ n = 5753 ∨ n = 5755 ∨ n = 5757 ∨ n = 5759 ∨ n = 5761 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨10, witness_of_certificate certificate_5695⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5697⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5699⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5701⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5703⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5705⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5707⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5709⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5711⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5713⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5715⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5717⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5719⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5721⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5723⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5725⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5727⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5729⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5731⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5733⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_5735⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5737⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5739⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5741⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5743⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5745⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5747⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5749⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5751⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5753⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5755⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5757⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_5759⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5761⟩

end Collatz.Research.CoefficientDescent.Batch086
