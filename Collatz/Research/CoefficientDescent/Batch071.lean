import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch071

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4691. -/
theorem certificate_4691 : classCertificateB 4 4691 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4691 (m : Nat) : stoppingTime (2 ^ 4 * m + 4691) 4 :=
  stoppingTime_of_classCertificate certificate_4691 m

/-- Checked base and every prefix for input 4693. -/
theorem certificate_4693 : classCertificateB 2 4693 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4693 (m : Nat) : stoppingTime (2 ^ 2 * m + 4693) 2 :=
  stoppingTime_of_classCertificate certificate_4693 m

/-- Checked base and every prefix for input 4695. -/
theorem certificate_4695 : classCertificateB 5 4695 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4695 (m : Nat) : stoppingTime (2 ^ 5 * m + 4695) 5 :=
  stoppingTime_of_classCertificate certificate_4695 m

/-- Checked base and every prefix for input 4697. -/
theorem certificate_4697 : classCertificateB 2 4697 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4697 (m : Nat) : stoppingTime (2 ^ 2 * m + 4697) 2 :=
  stoppingTime_of_classCertificate certificate_4697 m

/-- Checked base and every prefix for input 4699. -/
theorem certificate_4699 : classCertificateB 21 4699 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4699 (m : Nat) : stoppingTime (2 ^ 21 * m + 4699) 21 :=
  stoppingTime_of_classCertificate certificate_4699 m

/-- Checked base and every prefix for input 4701. -/
theorem certificate_4701 : classCertificateB 2 4701 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4701 (m : Nat) : stoppingTime (2 ^ 2 * m + 4701) 2 :=
  stoppingTime_of_classCertificate certificate_4701 m

/-- Checked base and every prefix for input 4703. -/
theorem certificate_4703 : classCertificateB 8 4703 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4703 (m : Nat) : stoppingTime (2 ^ 8 * m + 4703) 8 :=
  stoppingTime_of_classCertificate certificate_4703 m

/-- Checked base and every prefix for input 4705. -/
theorem certificate_4705 : classCertificateB 2 4705 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4705 (m : Nat) : stoppingTime (2 ^ 2 * m + 4705) 2 :=
  stoppingTime_of_classCertificate certificate_4705 m

/-- Checked base and every prefix for input 4707. -/
theorem certificate_4707 : classCertificateB 4 4707 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4707 (m : Nat) : stoppingTime (2 ^ 4 * m + 4707) 4 :=
  stoppingTime_of_classCertificate certificate_4707 m

/-- Checked base and every prefix for input 4709. -/
theorem certificate_4709 : classCertificateB 2 4709 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4709 (m : Nat) : stoppingTime (2 ^ 2 * m + 4709) 2 :=
  stoppingTime_of_classCertificate certificate_4709 m

/-- Checked base and every prefix for input 4711. -/
theorem certificate_4711 : classCertificateB 12 4711 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4711 (m : Nat) : stoppingTime (2 ^ 12 * m + 4711) 12 :=
  stoppingTime_of_classCertificate certificate_4711 m

/-- Checked base and every prefix for input 4713. -/
theorem certificate_4713 : classCertificateB 2 4713 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4713 (m : Nat) : stoppingTime (2 ^ 2 * m + 4713) 2 :=
  stoppingTime_of_classCertificate certificate_4713 m

/-- Checked base and every prefix for input 4715. -/
theorem certificate_4715 : classCertificateB 5 4715 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4715 (m : Nat) : stoppingTime (2 ^ 5 * m + 4715) 5 :=
  stoppingTime_of_classCertificate certificate_4715 m

/-- Checked base and every prefix for input 4717. -/
theorem certificate_4717 : classCertificateB 2 4717 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4717 (m : Nat) : stoppingTime (2 ^ 2 * m + 4717) 2 :=
  stoppingTime_of_classCertificate certificate_4717 m

/-- Checked base and every prefix for input 4719. -/
theorem certificate_4719 : classCertificateB 23 4719 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4719 (m : Nat) : stoppingTime (2 ^ 23 * m + 4719) 23 :=
  stoppingTime_of_classCertificate certificate_4719 m

/-- Checked base and every prefix for input 4721. -/
theorem certificate_4721 : classCertificateB 2 4721 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4721 (m : Nat) : stoppingTime (2 ^ 2 * m + 4721) 2 :=
  stoppingTime_of_classCertificate certificate_4721 m

/-- Checked base and every prefix for input 4723. -/
theorem certificate_4723 : classCertificateB 4 4723 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4723 (m : Nat) : stoppingTime (2 ^ 4 * m + 4723) 4 :=
  stoppingTime_of_classCertificate certificate_4723 m

/-- Checked base and every prefix for input 4725. -/
theorem certificate_4725 : classCertificateB 2 4725 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4725 (m : Nat) : stoppingTime (2 ^ 2 * m + 4725) 2 :=
  stoppingTime_of_classCertificate certificate_4725 m

/-- Checked base and every prefix for input 4727. -/
theorem certificate_4727 : classCertificateB 5 4727 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4727 (m : Nat) : stoppingTime (2 ^ 5 * m + 4727) 5 :=
  stoppingTime_of_classCertificate certificate_4727 m

/-- Checked base and every prefix for input 4729. -/
theorem certificate_4729 : classCertificateB 2 4729 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4729 (m : Nat) : stoppingTime (2 ^ 2 * m + 4729) 2 :=
  stoppingTime_of_classCertificate certificate_4729 m

/-- Checked base and every prefix for input 4731. -/
theorem certificate_4731 : classCertificateB 8 4731 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4731 (m : Nat) : stoppingTime (2 ^ 8 * m + 4731) 8 :=
  stoppingTime_of_classCertificate certificate_4731 m

/-- Checked base and every prefix for input 4733. -/
theorem certificate_4733 : classCertificateB 2 4733 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4733 (m : Nat) : stoppingTime (2 ^ 2 * m + 4733) 2 :=
  stoppingTime_of_classCertificate certificate_4733 m

/-- Checked base and every prefix for input 4735. -/
theorem certificate_4735 : classCertificateB 21 4735 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4735 (m : Nat) : stoppingTime (2 ^ 21 * m + 4735) 21 :=
  stoppingTime_of_classCertificate certificate_4735 m

/-- Checked base and every prefix for input 4737. -/
theorem certificate_4737 : classCertificateB 2 4737 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4737 (m : Nat) : stoppingTime (2 ^ 2 * m + 4737) 2 :=
  stoppingTime_of_classCertificate certificate_4737 m

/-- Checked base and every prefix for input 4739. -/
theorem certificate_4739 : classCertificateB 4 4739 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4739 (m : Nat) : stoppingTime (2 ^ 4 * m + 4739) 4 :=
  stoppingTime_of_classCertificate certificate_4739 m

/-- Checked base and every prefix for input 4741. -/
theorem certificate_4741 : classCertificateB 2 4741 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4741 (m : Nat) : stoppingTime (2 ^ 2 * m + 4741) 2 :=
  stoppingTime_of_classCertificate certificate_4741 m

/-- Checked base and every prefix for input 4743. -/
theorem certificate_4743 : classCertificateB 7 4743 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4743 (m : Nat) : stoppingTime (2 ^ 7 * m + 4743) 7 :=
  stoppingTime_of_classCertificate certificate_4743 m

/-- Checked base and every prefix for input 4745. -/
theorem certificate_4745 : classCertificateB 2 4745 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4745 (m : Nat) : stoppingTime (2 ^ 2 * m + 4745) 2 :=
  stoppingTime_of_classCertificate certificate_4745 m

/-- Checked base and every prefix for input 4747. -/
theorem certificate_4747 : classCertificateB 5 4747 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4747 (m : Nat) : stoppingTime (2 ^ 5 * m + 4747) 5 :=
  stoppingTime_of_classCertificate certificate_4747 m

/-- Checked base and every prefix for input 4749. -/
theorem certificate_4749 : classCertificateB 2 4749 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4749 (m : Nat) : stoppingTime (2 ^ 2 * m + 4749) 2 :=
  stoppingTime_of_classCertificate certificate_4749 m

/-- Checked base and every prefix for input 4751. -/
theorem certificate_4751 : classCertificateB 7 4751 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4751 (m : Nat) : stoppingTime (2 ^ 7 * m + 4751) 7 :=
  stoppingTime_of_classCertificate certificate_4751 m

/-- Checked base and every prefix for input 4753. -/
theorem certificate_4753 : classCertificateB 2 4753 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4753 (m : Nat) : stoppingTime (2 ^ 2 * m + 4753) 2 :=
  stoppingTime_of_classCertificate certificate_4753 m

/-- Checked base and every prefix for input 4755. -/
theorem certificate_4755 : classCertificateB 4 4755 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4755 (m : Nat) : stoppingTime (2 ^ 4 * m + 4755) 4 :=
  stoppingTime_of_classCertificate certificate_4755 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4691 4757 := by
  intro n hlo hhi hodd
  have hn : n = 4691 ∨ n = 4693 ∨ n = 4695 ∨ n = 4697 ∨ n = 4699 ∨ n = 4701 ∨ n = 4703 ∨ n = 4705 ∨ n = 4707 ∨ n = 4709 ∨ n = 4711 ∨ n = 4713 ∨ n = 4715 ∨ n = 4717 ∨ n = 4719 ∨ n = 4721 ∨ n = 4723 ∨ n = 4725 ∨ n = 4727 ∨ n = 4729 ∨ n = 4731 ∨ n = 4733 ∨ n = 4735 ∨ n = 4737 ∨ n = 4739 ∨ n = 4741 ∨ n = 4743 ∨ n = 4745 ∨ n = 4747 ∨ n = 4749 ∨ n = 4751 ∨ n = 4753 ∨ n = 4755 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_4691⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4693⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4695⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4697⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_4699⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4701⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4703⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4705⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4707⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4709⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_4711⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4713⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4715⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4717⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_4719⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4721⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4723⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4725⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4727⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4729⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4731⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4733⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_4735⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4737⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4739⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4741⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4743⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4745⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4747⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4749⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4751⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4753⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4755⟩

end Collatz.Research.CoefficientDescent.Batch071
