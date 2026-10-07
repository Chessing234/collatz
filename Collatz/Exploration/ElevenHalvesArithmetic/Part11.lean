import Collatz.Exploration.ElevenHalvesArithmetic.Part10

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `0100101001001010010101`. -/
theorem parameters_0100101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+5746 ∧ x1 = 8192*q+2873 ∧ x2 = 24576*q+8620 ∧ x3 = 12288*q+4310 ∧ x4 = 6144*q+2155 ∧ x5 = 18432*q+6466 ∧ x6 = 9216*q+3233 ∧ x7 = 27648*q+9700 ∧ x8 = 13824*q+4850 ∧ x9 = 6912*q+2425 ∧ x10 = 20736*q+7276 ∧ x11 = 10368*q+3638 ∧ x12 = 5184*q+1819 ∧ x13 = 15552*q+5458 ∧ x14 = 7776*q+2729 ∧ x15 = 23328*q+8188 ∧ x16 = 11664*q+4094 ∧ x17 = 5832*q+2047 ∧ x18 = 17496*q+6142 ∧ x19 = 8748*q+3071 ∧ x20 = 26244*q+9214 ∧ x21 = 13122*q+4607 ∧ x22 = 39366*q+13822 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010100`. -/
theorem parameters_0100101001010010010100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 16384*q+5106 ∧ x1 = 8192*q+2553 ∧ x2 = 24576*q+7660 ∧ x3 = 12288*q+3830 ∧ x4 = 6144*q+1915 ∧ x5 = 18432*q+5746 ∧ x6 = 9216*q+2873 ∧ x7 = 27648*q+8620 ∧ x8 = 13824*q+4310 ∧ x9 = 6912*q+2155 ∧ x10 = 20736*q+6466 ∧ x11 = 10368*q+3233 ∧ x12 = 31104*q+9700 ∧ x13 = 15552*q+4850 ∧ x14 = 7776*q+2425 ∧ x15 = 23328*q+7276 ∧ x16 = 11664*q+3638 ∧ x17 = 5832*q+1819 ∧ x18 = 17496*q+5458 ∧ x19 = 8748*q+2729 ∧ x20 = 26244*q+8188 ∧ x21 = 13122*q+4094 ∧ x22 = 6561*q+2047 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010010100101001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010101`. -/
theorem parameters_0100101001010010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+13298 ∧ x1 = 8192*q+6649 ∧ x2 = 24576*q+19948 ∧ x3 = 12288*q+9974 ∧ x4 = 6144*q+4987 ∧ x5 = 18432*q+14962 ∧ x6 = 9216*q+7481 ∧ x7 = 27648*q+22444 ∧ x8 = 13824*q+11222 ∧ x9 = 6912*q+5611 ∧ x10 = 20736*q+16834 ∧ x11 = 10368*q+8417 ∧ x12 = 31104*q+25252 ∧ x13 = 15552*q+12626 ∧ x14 = 7776*q+6313 ∧ x15 = 23328*q+18940 ∧ x16 = 11664*q+9470 ∧ x17 = 5832*q+4735 ∧ x18 = 17496*q+14206 ∧ x19 = 8748*q+7103 ∧ x20 = 26244*q+21310 ∧ x21 = 13122*q+10655 ∧ x22 = 39366*q+31966 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010010100101001001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0101001001010010100100`. -/
theorem parameters_0101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 16384*q+6358 ∧ x1 = 8192*q+3179 ∧ x2 = 24576*q+9538 ∧ x3 = 12288*q+4769 ∧ x4 = 36864*q+14308 ∧ x5 = 18432*q+7154 ∧ x6 = 9216*q+3577 ∧ x7 = 27648*q+10732 ∧ x8 = 13824*q+5366 ∧ x9 = 6912*q+2683 ∧ x10 = 20736*q+8050 ∧ x11 = 10368*q+4025 ∧ x12 = 31104*q+12076 ∧ x13 = 15552*q+6038 ∧ x14 = 7776*q+3019 ∧ x15 = 23328*q+9058 ∧ x16 = 11664*q+4529 ∧ x17 = 34992*q+13588 ∧ x18 = 17496*q+6794 ∧ x19 = 8748*q+3397 ∧ x20 = 26244*q+10192 ∧ x21 = 13122*q+5096 ∧ x22 = 6561*q+2548 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0101001001010010100101`. -/
theorem parameters_0101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+14550 ∧ x1 = 8192*q+7275 ∧ x2 = 24576*q+21826 ∧ x3 = 12288*q+10913 ∧ x4 = 36864*q+32740 ∧ x5 = 18432*q+16370 ∧ x6 = 9216*q+8185 ∧ x7 = 27648*q+24556 ∧ x8 = 13824*q+12278 ∧ x9 = 6912*q+6139 ∧ x10 = 20736*q+18418 ∧ x11 = 10368*q+9209 ∧ x12 = 31104*q+27628 ∧ x13 = 15552*q+13814 ∧ x14 = 7776*q+6907 ∧ x15 = 23328*q+20722 ∧ x16 = 11664*q+10361 ∧ x17 = 34992*q+31084 ∧ x18 = 17496*q+15542 ∧ x19 = 8748*q+7771 ∧ x20 = 26244*q+23314 ∧ x21 = 13122*q+11657 ∧ x22 = 39366*q+34972 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0101001010010010100100`. -/
theorem parameters_0101001010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 16384*q+12022 ∧ x1 = 8192*q+6011 ∧ x2 = 24576*q+18034 ∧ x3 = 12288*q+9017 ∧ x4 = 36864*q+27052 ∧ x5 = 18432*q+13526 ∧ x6 = 9216*q+6763 ∧ x7 = 27648*q+20290 ∧ x8 = 13824*q+10145 ∧ x9 = 41472*q+30436 ∧ x10 = 20736*q+15218 ∧ x11 = 10368*q+7609 ∧ x12 = 31104*q+22828 ∧ x13 = 15552*q+11414 ∧ x14 = 7776*q+5707 ∧ x15 = 23328*q+17122 ∧ x16 = 11664*q+8561 ∧ x17 = 34992*q+25684 ∧ x18 = 17496*q+12842 ∧ x19 = 8748*q+6421 ∧ x20 = 26244*q+19264 ∧ x21 = 13122*q+9632 ∧ x22 = 6561*q+4816 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `0101001010010010100101`. -/
theorem parameters_0101001010010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+3830 ∧ x1 = 8192*q+1915 ∧ x2 = 24576*q+5746 ∧ x3 = 12288*q+2873 ∧ x4 = 36864*q+8620 ∧ x5 = 18432*q+4310 ∧ x6 = 9216*q+2155 ∧ x7 = 27648*q+6466 ∧ x8 = 13824*q+3233 ∧ x9 = 41472*q+9700 ∧ x10 = 20736*q+4850 ∧ x11 = 10368*q+2425 ∧ x12 = 31104*q+7276 ∧ x13 = 15552*q+3638 ∧ x14 = 7776*q+1819 ∧ x15 = 23328*q+5458 ∧ x16 = 11664*q+2729 ∧ x17 = 34992*q+8188 ∧ x18 = 17496*q+4094 ∧ x19 = 8748*q+2047 ∧ x20 = 26244*q+6142 ∧ x21 = 13122*q+3071 ∧ x22 = 39366*q+9214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `1001010010010100101000`. -/
theorem parameters_1001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 16384*q+6969 ∧ x1 = 49152*q+20908 ∧ x2 = 24576*q+10454 ∧ x3 = 12288*q+5227 ∧ x4 = 36864*q+15682 ∧ x5 = 18432*q+7841 ∧ x6 = 55296*q+23524 ∧ x7 = 27648*q+11762 ∧ x8 = 13824*q+5881 ∧ x9 = 41472*q+17644 ∧ x10 = 20736*q+8822 ∧ x11 = 10368*q+4411 ∧ x12 = 31104*q+13234 ∧ x13 = 15552*q+6617 ∧ x14 = 46656*q+19852 ∧ x15 = 23328*q+9926 ∧ x16 = 11664*q+4963 ∧ x17 = 34992*q+14890 ∧ x18 = 17496*q+7445 ∧ x19 = 52488*q+22336 ∧ x20 = 26244*q+11168 ∧ x21 = 13122*q+5584 ∧ x22 = 6561*q+2792 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `1001010010010100101001`. -/
theorem parameters_1001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+15161 ∧ x1 = 49152*q+45484 ∧ x2 = 24576*q+22742 ∧ x3 = 12288*q+11371 ∧ x4 = 36864*q+34114 ∧ x5 = 18432*q+17057 ∧ x6 = 55296*q+51172 ∧ x7 = 27648*q+25586 ∧ x8 = 13824*q+12793 ∧ x9 = 41472*q+38380 ∧ x10 = 20736*q+19190 ∧ x11 = 10368*q+9595 ∧ x12 = 31104*q+28786 ∧ x13 = 15552*q+14393 ∧ x14 = 46656*q+43180 ∧ x15 = 23328*q+21590 ∧ x16 = 11664*q+10795 ∧ x17 = 34992*q+32386 ∧ x18 = 17496*q+16193 ∧ x19 = 52488*q+48580 ∧ x20 = 26244*q+24290 ∧ x21 = 13122*q+12145 ∧ x22 = 39366*q+36436 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `1001010010100100101000`. -/
theorem parameters_1001010010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 16384*q+10745 ∧ x1 = 49152*q+32236 ∧ x2 = 24576*q+16118 ∧ x3 = 12288*q+8059 ∧ x4 = 36864*q+24178 ∧ x5 = 18432*q+12089 ∧ x6 = 55296*q+36268 ∧ x7 = 27648*q+18134 ∧ x8 = 13824*q+9067 ∧ x9 = 41472*q+27202 ∧ x10 = 20736*q+13601 ∧ x11 = 62208*q+40804 ∧ x12 = 31104*q+20402 ∧ x13 = 15552*q+10201 ∧ x14 = 46656*q+30604 ∧ x15 = 23328*q+15302 ∧ x16 = 11664*q+7651 ∧ x17 = 34992*q+22954 ∧ x18 = 17496*q+11477 ∧ x19 = 52488*q+34432 ∧ x20 = 26244*q+17216 ∧ x21 = 13122*q+8608 ∧ x22 = 6561*q+4304 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_100101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `1001010010100100101001`. -/
theorem parameters_1001010010100100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (x22 = 3*x21+1 ∧ x21%2 = 1))
    : ∃ q : Nat, x0 = 16384*q+2553 ∧ x1 = 49152*q+7660 ∧ x2 = 24576*q+3830 ∧ x3 = 12288*q+1915 ∧ x4 = 36864*q+5746 ∧ x5 = 18432*q+2873 ∧ x6 = 55296*q+8620 ∧ x7 = 27648*q+4310 ∧ x8 = 13824*q+2155 ∧ x9 = 41472*q+6466 ∧ x10 = 20736*q+3233 ∧ x11 = 62208*q+9700 ∧ x12 = 31104*q+4850 ∧ x13 = 15552*q+2425 ∧ x14 = 46656*q+7276 ∧ x15 = 23328*q+3638 ∧ x16 = 11664*q+1819 ∧ x17 = 34992*q+5458 ∧ x18 = 17496*q+2729 ∧ x19 = 52488*q+8188 ∧ x20 = 26244*q+4094 ∧ x21 = 13122*q+2047 ∧ x22 = 39366*q+6142 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_100101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `1010010100100101001010`. -/
theorem parameters_1010010100100101001010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Nat)
    (r0 : (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0))
    (r18 : (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    : ∃ q : Nat, x0 = 8192*q+1915 ∧ x1 = 24576*q+5746 ∧ x2 = 12288*q+2873 ∧ x3 = 36864*q+8620 ∧ x4 = 18432*q+4310 ∧ x5 = 9216*q+2155 ∧ x6 = 27648*q+6466 ∧ x7 = 13824*q+3233 ∧ x8 = 41472*q+9700 ∧ x9 = 20736*q+4850 ∧ x10 = 10368*q+2425 ∧ x11 = 31104*q+7276 ∧ x12 = 15552*q+3638 ∧ x13 = 7776*q+1819 ∧ x14 = 23328*q+5458 ∧ x15 = 11664*q+2729 ∧ x16 = 34992*q+8188 ∧ x17 = 17496*q+4094 ∧ x18 = 8748*q+2047 ∧ x19 = 26244*q+6142 ∧ x20 = 13122*q+3071 ∧ x21 = 39366*q+9214 ∧ x22 = 19683*q+4607 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21⟩ := parameters_101001010010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
  have hstep := r21.1
  have hparity := r21.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15
  · exact p16
  · exact p17
  · exact p18
  · exact p19
  · exact p20
  · exact p21
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    omega

/-- Exact source residue and full affine trace for branch `00101001001010010100100`. -/
theorem parameters_00101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    : ∃ q : Nat, x0 = 32768*q+12716 ∧ x1 = 16384*q+6358 ∧ x2 = 8192*q+3179 ∧ x3 = 24576*q+9538 ∧ x4 = 12288*q+4769 ∧ x5 = 36864*q+14308 ∧ x6 = 18432*q+7154 ∧ x7 = 9216*q+3577 ∧ x8 = 27648*q+10732 ∧ x9 = 13824*q+5366 ∧ x10 = 6912*q+2683 ∧ x11 = 20736*q+8050 ∧ x12 = 10368*q+4025 ∧ x13 = 31104*q+12076 ∧ x14 = 15552*q+6038 ∧ x15 = 7776*q+3019 ∧ x16 = 23328*q+9058 ∧ x17 = 11664*q+4529 ∧ x18 = 34992*q+13588 ∧ x19 = 17496*q+6794 ∧ x20 = 8748*q+3397 ∧ x21 = 26244*q+10192 ∧ x22 = 13122*q+5096 ∧ x23 = 6561*q+2548 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `00101001001010010100101`. -/
theorem parameters_00101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    : ∃ q : Nat, x0 = 32768*q+29100 ∧ x1 = 16384*q+14550 ∧ x2 = 8192*q+7275 ∧ x3 = 24576*q+21826 ∧ x4 = 12288*q+10913 ∧ x5 = 36864*q+32740 ∧ x6 = 18432*q+16370 ∧ x7 = 9216*q+8185 ∧ x8 = 27648*q+24556 ∧ x9 = 13824*q+12278 ∧ x10 = 6912*q+6139 ∧ x11 = 20736*q+18418 ∧ x12 = 10368*q+9209 ∧ x13 = 31104*q+27628 ∧ x14 = 15552*q+13814 ∧ x15 = 7776*q+6907 ∧ x16 = 23328*q+20722 ∧ x17 = 11664*q+10361 ∧ x18 = 34992*q+31084 ∧ x19 = 17496*q+15542 ∧ x20 = 8748*q+7771 ∧ x21 = 26244*q+23314 ∧ x22 = 13122*q+11657 ∧ x23 = 39366*q+34972 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010100100`. -/
theorem parameters_00101001010010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    : ∃ q : Nat, x0 = 32768*q+24044 ∧ x1 = 16384*q+12022 ∧ x2 = 8192*q+6011 ∧ x3 = 24576*q+18034 ∧ x4 = 12288*q+9017 ∧ x5 = 36864*q+27052 ∧ x6 = 18432*q+13526 ∧ x7 = 9216*q+6763 ∧ x8 = 27648*q+20290 ∧ x9 = 13824*q+10145 ∧ x10 = 41472*q+30436 ∧ x11 = 20736*q+15218 ∧ x12 = 10368*q+7609 ∧ x13 = 31104*q+22828 ∧ x14 = 15552*q+11414 ∧ x15 = 7776*q+5707 ∧ x16 = 23328*q+17122 ∧ x17 = 11664*q+8561 ∧ x18 = 34992*q+25684 ∧ x19 = 17496*q+12842 ∧ x20 = 8748*q+6421 ∧ x21 = 26244*q+19264 ∧ x22 = 13122*q+9632 ∧ x23 = 6561*q+4816 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `00101001010010010100101`. -/
theorem parameters_00101001010010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0))
    (r15 : (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0))
    (r20 : (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    : ∃ q : Nat, x0 = 32768*q+7660 ∧ x1 = 16384*q+3830 ∧ x2 = 8192*q+1915 ∧ x3 = 24576*q+5746 ∧ x4 = 12288*q+2873 ∧ x5 = 36864*q+8620 ∧ x6 = 18432*q+4310 ∧ x7 = 9216*q+2155 ∧ x8 = 27648*q+6466 ∧ x9 = 13824*q+3233 ∧ x10 = 41472*q+9700 ∧ x11 = 20736*q+4850 ∧ x12 = 10368*q+2425 ∧ x13 = 31104*q+7276 ∧ x14 = 15552*q+3638 ∧ x15 = 7776*q+1819 ∧ x16 = 23328*q+5458 ∧ x17 = 11664*q+2729 ∧ x18 = 34992*q+8188 ∧ x19 = 17496*q+4094 ∧ x20 = 8748*q+2047 ∧ x21 = 26244*q+6142 ∧ x22 = 13122*q+3071 ∧ x23 = 39366*q+9214 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0010100101001001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `01001010010010100101000`. -/
theorem parameters_01001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    : ∃ q : Nat, x0 = 32768*q+13938 ∧ x1 = 16384*q+6969 ∧ x2 = 49152*q+20908 ∧ x3 = 24576*q+10454 ∧ x4 = 12288*q+5227 ∧ x5 = 36864*q+15682 ∧ x6 = 18432*q+7841 ∧ x7 = 55296*q+23524 ∧ x8 = 27648*q+11762 ∧ x9 = 13824*q+5881 ∧ x10 = 41472*q+17644 ∧ x11 = 20736*q+8822 ∧ x12 = 10368*q+4411 ∧ x13 = 31104*q+13234 ∧ x14 = 15552*q+6617 ∧ x15 = 46656*q+19852 ∧ x16 = 23328*q+9926 ∧ x17 = 11664*q+4963 ∧ x18 = 34992*q+14890 ∧ x19 = 17496*q+7445 ∧ x20 = 52488*q+22336 ∧ x21 = 26244*q+11168 ∧ x22 = 13122*q+5584 ∧ x23 = 6561*q+2792 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `01001010010010100101001`. -/
theorem parameters_01001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0))
    (r12 : (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    : ∃ q : Nat, x0 = 32768*q+30322 ∧ x1 = 16384*q+15161 ∧ x2 = 49152*q+45484 ∧ x3 = 24576*q+22742 ∧ x4 = 12288*q+11371 ∧ x5 = 36864*q+34114 ∧ x6 = 18432*q+17057 ∧ x7 = 55296*q+51172 ∧ x8 = 27648*q+25586 ∧ x9 = 13824*q+12793 ∧ x10 = 41472*q+38380 ∧ x11 = 20736*q+19190 ∧ x12 = 10368*q+9595 ∧ x13 = 31104*q+28786 ∧ x14 = 15552*q+14393 ∧ x15 = 46656*q+43180 ∧ x16 = 23328*q+21590 ∧ x17 = 11664*q+10795 ∧ x18 = 34992*q+32386 ∧ x19 = 17496*q+16193 ∧ x20 = 52488*q+48580 ∧ x21 = 26244*q+24290 ∧ x22 = 13122*q+12145 ∧ x23 = 39366*q+36436 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega

/-- Exact source residue and full affine trace for branch `01001010010100100101000`. -/
theorem parameters_01001010010100100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : Nat)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    (r6 : (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    (r11 : (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0))
    (r14 : (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0))
    (r17 : (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0))
    (r19 : (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    : ∃ q : Nat, x0 = 32768*q+21490 ∧ x1 = 16384*q+10745 ∧ x2 = 49152*q+32236 ∧ x3 = 24576*q+16118 ∧ x4 = 12288*q+8059 ∧ x5 = 36864*q+24178 ∧ x6 = 18432*q+12089 ∧ x7 = 55296*q+36268 ∧ x8 = 27648*q+18134 ∧ x9 = 13824*q+9067 ∧ x10 = 41472*q+27202 ∧ x11 = 20736*q+13601 ∧ x12 = 62208*q+40804 ∧ x13 = 31104*q+20402 ∧ x14 = 15552*q+10201 ∧ x15 = 46656*q+30604 ∧ x16 = 23328*q+15302 ∧ x17 = 11664*q+7651 ∧ x18 = 34992*q+22954 ∧ x19 = 17496*q+11477 ∧ x20 = 52488*q+34432 ∧ x21 = 26244*q+17216 ∧ x22 = 13122*q+8608 ∧ x23 = 6561*q+4304 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22⟩ := parameters_0100101001010010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
  have hstep := r22.1
  have hparity := r22.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p0 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p1 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p2 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p3 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p4 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p5 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p6 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p7 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p8 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p9 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p10 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p11 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p12 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p13 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p14 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p15 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p16 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p17 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p18 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p19 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p20 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p21 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p22 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21
    omega


end Collatz.Exploration.ElevenHalvesArithmetic
