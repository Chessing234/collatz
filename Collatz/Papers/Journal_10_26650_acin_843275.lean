import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mert Özkenar, "Collatz Konjektürü’nün Bilgisayar Programı ile Hesaplanmasında Parite Sekansı Yöntemi Yaklaşımı", 2020.

Title: Collatz Konjektürü’nün Bilgisayar Programı ile Hesaplanmasında Parite Sekansı Yöntemi Yaklaşımı

Abstract (from harvested metadata, truncated):
Bu makalede, collatz konjektürü’nün bilgisayar programı ile hesaplamasında parite sekansı yöntemi yaklaşımı anlatılmıştır. Collatz konjektürüne dair kapsamlı araştırmalar ve çalışmalar yapılmış, tüm bilgilerin makalede yer alması amaçlanmıştır. Collatz konjektürünün hesaplanmasında kullanılacak olan parite sekansı yöntemi üzerinde çalışılmıştır. Yöntem için metodoloji oluşturulmuş, bilgisayar programları geliştirilmiş, sonuçlar bilgisayar çıktıları ve çıktılardan oluşan tablolar olarak paylaşılmış ve grafikler ile zenginleştirilmiştir. Collatz konjektürünün hesaplanmasına yönelik standart yöntemler karşılaştırılmış ve yöntem önerisinde bulunulmuştur. Üzerinde çalışılan yöntemlerin bilgisayar...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.26650/acin.843275
-/

namespace Collatz.Papers.Journal_10_26650_acin_843275

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mert Özkenar, \"Collatz Konjektürü’nün Bilgisayar Programı ile Hesaplanmasında Parite Sekansı Yöntemi Yaklaşımı\", Acta Infologica, DOI:10.26650/acin.843275 [2020]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_26650_acin_843275
