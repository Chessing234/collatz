import Collatz.Structure.CycleModThree
import Collatz.Structure.CycleExtremes
import Collatz.Structure.CycleMinClass

/-!
# The residue class of a cycle's greatest point

The least point of a cycle was pinned to two classes modulo twelve.  The
greatest point can be pinned too, by looking at what *precedes* it.

**The predecessor of the maximum is odd.**  Let `M` be the greatest point and
`p` its predecessor on the cycle, so `T(p) = M`.  If `p` were even then
`T(p) = p/2`, giving `p = 2M > M` — a cycle point above the maximum, which is
impossible.  So `p` is odd and `M = (3p+1)/2`.

**Hence `M ≡ 2 (mod 3)`.**  `CycleModThree.accStep_mod_three_of_odd` says the
image of the odd branch is always `2` modulo `3`, and `M` is such an image.

Combined with `CycleExtremes.cycleMax_even`, the greatest point of a
hypothetical cycle satisfies

**`M ≡ 2 (mod 6)`.**

So both extremes are now confined: the least point to `7, 11 mod 12`, the
greatest to `2 mod 6`.
-/

namespace Collatz
namespace CycleMaxClass

open Reach AccCycle CycleExtremes

/-! ## The predecessor of the greatest point -/

/-- The point preceding index `i` on a cycle, reached by going `L - 1` further
around. -/
theorem accStep_pred {n L i : Nat} (h : AccIsCycleOf n L) :
    acceleratedStep (acceleratedOrbit (i + L - 1) n) = acceleratedOrbit i n := by
  have hL := h.1
  have hidx : i + L - 1 + 1 = i + L := by omega
  have hstep : acceleratedStep (acceleratedOrbit (i + L - 1) n)
      = acceleratedOrbit (i + L - 1 + 1) n := (acceleratedOrbit_succ_step _ _).symm
  rw [hstep, hidx]
  calc acceleratedOrbit (i + L) n
      = acceleratedOrbit i (acceleratedOrbit L n) := (acceleratedOrbit_add i L n).symm
    _ = acceleratedOrbit i n := by rw [h.2]

/-- **The predecessor of the greatest point is odd.**  An even predecessor would
be twice the maximum, hence a cycle point above it. -/
theorem pred_of_cycleMax_odd {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    ∃ p : Nat, acceleratedStep p = cycleMax n L ∧ p % 2 = 1 ∧
      p ≤ cycleMax n L := by
  obtain ⟨i, _, hval⟩ := cycleMax_attained h
  refine ⟨acceleratedOrbit (i + L - 1) n, ?_, ?_, ?_⟩
  · rw [accStep_pred h, ← hval]
  · -- an even predecessor would exceed the maximum
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (i + L - 1) n) with he | ho
    · exfalso
      have hstep : acceleratedStep (acceleratedOrbit (i + L - 1) n)
          = acceleratedOrbit (i + L - 1) n / 2 := by
        rw [acceleratedStep, if_pos he]
      have heq : acceleratedOrbit (i + L - 1) n / 2 = cycleMax n L := by
        rw [← hstep, accStep_pred h, ← hval]
      have hle := le_cycleMax h (i + L - 1)
      have hpos : 0 < cycleMax n L := cycleMax_pos hn h
      omega
    · exact ho
  · exact le_cycleMax h (i + L - 1)

/-! ## The residue of the greatest point -/

/-- **The greatest point of a cycle is `2` modulo `3`**, being the image of an
odd step. -/
theorem cycleMax_mod_three {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    cycleMax n L % 3 = 2 := by
  obtain ⟨p, hstep, hodd, _⟩ := pred_of_cycleMax_odd hn h
  rw [← hstep]
  exact CycleModThree.accStep_mod_three_of_odd hodd

/-- **The greatest point of a cycle is `2` modulo `6`**: even, and `2` modulo
`3`. -/
theorem cycleMax_mod_six {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    cycleMax n L % 6 = 2 := by
  have heven := cycleMax_even hn h
  have hthree := cycleMax_mod_three hn h
  omega

/-- The greatest point is not divisible by three — a special case of the
modulo-three theorem, recovered independently here. -/
theorem not_three_dvd_cycleMax {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    ¬ 3 ∣ cycleMax n L := by
  have := cycleMax_mod_three hn h
  omega

/-- Both extremes, classified: the least point is `7` or `11` modulo `12`, the
greatest is `2` modulo `6`. -/
theorem extremes_classified {n L m : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hmcyc : AccIsCycleOf m L) :
    (m % 12 = 7 ∨ m % 12 = 11) ∧ cycleMax n L % 6 = 2 :=
  ⟨CycleMinClass.cycleMin_mod_twelve hn hm hmin hgt hmcyc, cycleMax_mod_six hn h⟩

end CycleMaxClass
end Collatz
