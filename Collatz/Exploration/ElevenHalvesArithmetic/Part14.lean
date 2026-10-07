import Collatz.Exploration.ElevenHalvesArithmetic.Part13

namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- Exact source residue and full affine trace for branch `010010100101001001010010101`. -/
theorem parameters_010010100101001001010010101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    : ∃ q : Nat, x0 = 131072*q+5106 ∧ x1 = 65536*q+2553 ∧ x2 = 196608*q+7660 ∧ x3 = 98304*q+3830 ∧ x4 = 49152*q+1915 ∧ x5 = 147456*q+5746 ∧ x6 = 73728*q+2873 ∧ x7 = 221184*q+8620 ∧ x8 = 110592*q+4310 ∧ x9 = 55296*q+2155 ∧ x10 = 165888*q+6466 ∧ x11 = 82944*q+3233 ∧ x12 = 248832*q+9700 ∧ x13 = 124416*q+4850 ∧ x14 = 62208*q+2425 ∧ x15 = 186624*q+7276 ∧ x16 = 93312*q+3638 ∧ x17 = 46656*q+1819 ∧ x18 = 139968*q+5458 ∧ x19 = 69984*q+2729 ∧ x20 = 209952*q+8188 ∧ x21 = 104976*q+4094 ∧ x22 = 52488*q+2047 ∧ x23 = 157464*q+6142 ∧ x24 = 78732*q+3071 ∧ x25 = 236196*q+9214 ∧ x26 = 118098*q+4607 ∧ x27 = 354294*q+13822 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_01001010010100100101001010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `010100101001001010010100100`. -/
theorem parameters_010100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+20214 ∧ x1 = 65536*q+10107 ∧ x2 = 196608*q+30322 ∧ x3 = 98304*q+15161 ∧ x4 = 294912*q+45484 ∧ x5 = 147456*q+22742 ∧ x6 = 73728*q+11371 ∧ x7 = 221184*q+34114 ∧ x8 = 110592*q+17057 ∧ x9 = 331776*q+51172 ∧ x10 = 165888*q+25586 ∧ x11 = 82944*q+12793 ∧ x12 = 248832*q+38380 ∧ x13 = 124416*q+19190 ∧ x14 = 62208*q+9595 ∧ x15 = 186624*q+28786 ∧ x16 = 93312*q+14393 ∧ x17 = 279936*q+43180 ∧ x18 = 139968*q+21590 ∧ x19 = 69984*q+10795 ∧ x20 = 209952*q+32386 ∧ x21 = 104976*q+16193 ∧ x22 = 314928*q+48580 ∧ x23 = 157464*q+24290 ∧ x24 = 78732*q+12145 ∧ x25 = 236196*q+36436 ∧ x26 = 118098*q+18218 ∧ x27 = 59049*q+9109 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_01010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `010100101001001010010100101`. -/
theorem parameters_010100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    : ∃ q : Nat, x0 = 131072*q+85750 ∧ x1 = 65536*q+42875 ∧ x2 = 196608*q+128626 ∧ x3 = 98304*q+64313 ∧ x4 = 294912*q+192940 ∧ x5 = 147456*q+96470 ∧ x6 = 73728*q+48235 ∧ x7 = 221184*q+144706 ∧ x8 = 110592*q+72353 ∧ x9 = 331776*q+217060 ∧ x10 = 165888*q+108530 ∧ x11 = 82944*q+54265 ∧ x12 = 248832*q+162796 ∧ x13 = 124416*q+81398 ∧ x14 = 62208*q+40699 ∧ x15 = 186624*q+122098 ∧ x16 = 93312*q+61049 ∧ x17 = 279936*q+183148 ∧ x18 = 139968*q+91574 ∧ x19 = 69984*q+45787 ∧ x20 = 209952*q+137362 ∧ x21 = 104976*q+68681 ∧ x22 = 314928*q+206044 ∧ x23 = 157464*q+103022 ∧ x24 = 78732*q+51511 ∧ x25 = 236196*q+154534 ∧ x26 = 118098*q+77267 ∧ x27 = 354294*q+231802 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_01010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `100101001010010010100101000`. -/
theorem parameters_100101001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+35321 ∧ x1 = 393216*q+105964 ∧ x2 = 196608*q+52982 ∧ x3 = 98304*q+26491 ∧ x4 = 294912*q+79474 ∧ x5 = 147456*q+39737 ∧ x6 = 442368*q+119212 ∧ x7 = 221184*q+59606 ∧ x8 = 110592*q+29803 ∧ x9 = 331776*q+89410 ∧ x10 = 165888*q+44705 ∧ x11 = 497664*q+134116 ∧ x12 = 248832*q+67058 ∧ x13 = 124416*q+33529 ∧ x14 = 373248*q+100588 ∧ x15 = 186624*q+50294 ∧ x16 = 93312*q+25147 ∧ x17 = 279936*q+75442 ∧ x18 = 139968*q+37721 ∧ x19 = 419904*q+113164 ∧ x20 = 209952*q+56582 ∧ x21 = 104976*q+28291 ∧ x22 = 314928*q+84874 ∧ x23 = 157464*q+42437 ∧ x24 = 472392*q+127312 ∧ x25 = 236196*q+63656 ∧ x26 = 118098*q+31828 ∧ x27 = 59049*q+15914 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_10010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `100101001010010010100101001`. -/
theorem parameters_100101001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    : ∃ q : Nat, x0 = 131072*q+100857 ∧ x1 = 393216*q+302572 ∧ x2 = 196608*q+151286 ∧ x3 = 98304*q+75643 ∧ x4 = 294912*q+226930 ∧ x5 = 147456*q+113465 ∧ x6 = 442368*q+340396 ∧ x7 = 221184*q+170198 ∧ x8 = 110592*q+85099 ∧ x9 = 331776*q+255298 ∧ x10 = 165888*q+127649 ∧ x11 = 497664*q+382948 ∧ x12 = 248832*q+191474 ∧ x13 = 124416*q+95737 ∧ x14 = 373248*q+287212 ∧ x15 = 186624*q+143606 ∧ x16 = 93312*q+71803 ∧ x17 = 279936*q+215410 ∧ x18 = 139968*q+107705 ∧ x19 = 419904*q+323116 ∧ x20 = 209952*q+161558 ∧ x21 = 104976*q+80779 ∧ x22 = 314928*q+242338 ∧ x23 = 157464*q+121169 ∧ x24 = 472392*q+363508 ∧ x25 = 236196*q+181754 ∧ x26 = 118098*q+90877 ∧ x27 = 354294*q+272632 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26⟩ := parameters_10010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
  have hstep := r26.1
  have hparity := r26.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25
    omega

/-- Exact source residue and full affine trace for branch `0010100101001001010010100100`. -/
theorem parameters_0010100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
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
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    : ∃ q : Nat, x0 = 262144*q+40428 ∧ x1 = 131072*q+20214 ∧ x2 = 65536*q+10107 ∧ x3 = 196608*q+30322 ∧ x4 = 98304*q+15161 ∧ x5 = 294912*q+45484 ∧ x6 = 147456*q+22742 ∧ x7 = 73728*q+11371 ∧ x8 = 221184*q+34114 ∧ x9 = 110592*q+17057 ∧ x10 = 331776*q+51172 ∧ x11 = 165888*q+25586 ∧ x12 = 82944*q+12793 ∧ x13 = 248832*q+38380 ∧ x14 = 124416*q+19190 ∧ x15 = 62208*q+9595 ∧ x16 = 186624*q+28786 ∧ x17 = 93312*q+14393 ∧ x18 = 279936*q+43180 ∧ x19 = 139968*q+21590 ∧ x20 = 69984*q+10795 ∧ x21 = 209952*q+32386 ∧ x22 = 104976*q+16193 ∧ x23 = 314928*q+48580 ∧ x24 = 157464*q+24290 ∧ x25 = 78732*q+12145 ∧ x26 = 236196*q+36436 ∧ x27 = 118098*q+18218 ∧ x28 = 59049*q+9109 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hstep := r27.1
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega

/-- Exact source residue and full affine trace for branch `0010100101001001010010100101`. -/
theorem parameters_0010100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
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
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (x26 = 3*x25+1 ∧ x25%2 = 1))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    : ∃ q : Nat, x0 = 262144*q+171500 ∧ x1 = 131072*q+85750 ∧ x2 = 65536*q+42875 ∧ x3 = 196608*q+128626 ∧ x4 = 98304*q+64313 ∧ x5 = 294912*q+192940 ∧ x6 = 147456*q+96470 ∧ x7 = 73728*q+48235 ∧ x8 = 221184*q+144706 ∧ x9 = 110592*q+72353 ∧ x10 = 331776*q+217060 ∧ x11 = 165888*q+108530 ∧ x12 = 82944*q+54265 ∧ x13 = 248832*q+162796 ∧ x14 = 124416*q+81398 ∧ x15 = 62208*q+40699 ∧ x16 = 186624*q+122098 ∧ x17 = 93312*q+61049 ∧ x18 = 279936*q+183148 ∧ x19 = 139968*q+91574 ∧ x20 = 69984*q+45787 ∧ x21 = 209952*q+137362 ∧ x22 = 104976*q+68681 ∧ x23 = 314928*q+206044 ∧ x24 = 157464*q+103022 ∧ x25 = 78732*q+51511 ∧ x26 = 236196*q+154534 ∧ x27 = 118098*q+77267 ∧ x28 = 354294*q+231802 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hstep := r27.1
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010100101000`. -/
theorem parameters_0100101001010010010100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    : ∃ q : Nat, x0 = 262144*q+70642 ∧ x1 = 131072*q+35321 ∧ x2 = 393216*q+105964 ∧ x3 = 196608*q+52982 ∧ x4 = 98304*q+26491 ∧ x5 = 294912*q+79474 ∧ x6 = 147456*q+39737 ∧ x7 = 442368*q+119212 ∧ x8 = 221184*q+59606 ∧ x9 = 110592*q+29803 ∧ x10 = 331776*q+89410 ∧ x11 = 165888*q+44705 ∧ x12 = 497664*q+134116 ∧ x13 = 248832*q+67058 ∧ x14 = 124416*q+33529 ∧ x15 = 373248*q+100588 ∧ x16 = 186624*q+50294 ∧ x17 = 93312*q+25147 ∧ x18 = 279936*q+75442 ∧ x19 = 139968*q+37721 ∧ x20 = 419904*q+113164 ∧ x21 = 209952*q+56582 ∧ x22 = 104976*q+28291 ∧ x23 = 314928*q+84874 ∧ x24 = 157464*q+42437 ∧ x25 = 472392*q+127312 ∧ x26 = 236196*q+63656 ∧ x27 = 118098*q+31828 ∧ x28 = 59049*q+15914 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_010010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hstep := r27.1
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega

/-- Exact source residue and full affine trace for branch `0100101001010010010100101001`. -/
theorem parameters_0100101001010010010100101001
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    : ∃ q : Nat, x0 = 262144*q+201714 ∧ x1 = 131072*q+100857 ∧ x2 = 393216*q+302572 ∧ x3 = 196608*q+151286 ∧ x4 = 98304*q+75643 ∧ x5 = 294912*q+226930 ∧ x6 = 147456*q+113465 ∧ x7 = 442368*q+340396 ∧ x8 = 221184*q+170198 ∧ x9 = 110592*q+85099 ∧ x10 = 331776*q+255298 ∧ x11 = 165888*q+127649 ∧ x12 = 497664*q+382948 ∧ x13 = 248832*q+191474 ∧ x14 = 124416*q+95737 ∧ x15 = 373248*q+287212 ∧ x16 = 186624*q+143606 ∧ x17 = 93312*q+71803 ∧ x18 = 279936*q+215410 ∧ x19 = 139968*q+107705 ∧ x20 = 419904*q+323116 ∧ x21 = 209952*q+161558 ∧ x22 = 104976*q+80779 ∧ x23 = 314928*q+242338 ∧ x24 = 157464*q+121169 ∧ x25 = 472392*q+363508 ∧ x26 = 236196*q+181754 ∧ x27 = 118098*q+90877 ∧ x28 = 354294*q+272632 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_010010100101001001010010100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hstep := r27.1
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega

/-- Exact source residue and full affine trace for branch `1001010010100100101001010010`. -/
theorem parameters_1001010010100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    : ∃ q : Nat, x0 = 131072*q+100857 ∧ x1 = 393216*q+302572 ∧ x2 = 196608*q+151286 ∧ x3 = 98304*q+75643 ∧ x4 = 294912*q+226930 ∧ x5 = 147456*q+113465 ∧ x6 = 442368*q+340396 ∧ x7 = 221184*q+170198 ∧ x8 = 110592*q+85099 ∧ x9 = 331776*q+255298 ∧ x10 = 165888*q+127649 ∧ x11 = 497664*q+382948 ∧ x12 = 248832*q+191474 ∧ x13 = 124416*q+95737 ∧ x14 = 373248*q+287212 ∧ x15 = 186624*q+143606 ∧ x16 = 93312*q+71803 ∧ x17 = 279936*q+215410 ∧ x18 = 139968*q+107705 ∧ x19 = 419904*q+323116 ∧ x20 = 209952*q+161558 ∧ x21 = 104976*q+80779 ∧ x22 = 314928*q+242338 ∧ x23 = 157464*q+121169 ∧ x24 = 472392*q+363508 ∧ x25 = 236196*q+181754 ∧ x26 = 118098*q+90877 ∧ x27 = 354294*q+272632 ∧ x28 = 177147*q+136316 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27⟩ := parameters_100101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
  have hstep := r27.1
  have hparity := r27.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p22
  · exact p23
  · exact p24
  · exact p25
  · exact p26
  · exact p27
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26
    omega

/-- Exact source residue and full affine trace for branch `01001010010100100101001010010`. -/
theorem parameters_01001010010100100101001010010
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0))
    : ∃ q : Nat, x0 = 262144*q+201714 ∧ x1 = 131072*q+100857 ∧ x2 = 393216*q+302572 ∧ x3 = 196608*q+151286 ∧ x4 = 98304*q+75643 ∧ x5 = 294912*q+226930 ∧ x6 = 147456*q+113465 ∧ x7 = 442368*q+340396 ∧ x8 = 221184*q+170198 ∧ x9 = 110592*q+85099 ∧ x10 = 331776*q+255298 ∧ x11 = 165888*q+127649 ∧ x12 = 497664*q+382948 ∧ x13 = 248832*q+191474 ∧ x14 = 124416*q+95737 ∧ x15 = 373248*q+287212 ∧ x16 = 186624*q+143606 ∧ x17 = 93312*q+71803 ∧ x18 = 279936*q+215410 ∧ x19 = 139968*q+107705 ∧ x20 = 419904*q+323116 ∧ x21 = 209952*q+161558 ∧ x22 = 104976*q+80779 ∧ x23 = 314928*q+242338 ∧ x24 = 157464*q+121169 ∧ x25 = 472392*q+363508 ∧ x26 = 236196*q+181754 ∧ x27 = 118098*q+90877 ∧ x28 = 354294*q+272632 ∧ x29 = 177147*q+136316 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28⟩ := parameters_0100101001010010010100101001 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hstep := r28.1
  have hparity := r28.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  clear hparity
  refine ⟨q,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · exact p22
  · exact p23
  · exact p24
  · exact p25
  · exact p26
  · exact p27
  · exact p28
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27
    omega

/-- Exact source residue and full affine trace for branch `10010100101001001010010100100`. -/
theorem parameters_10010100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0))
    : ∃ q : Nat, x0 = 262144*q+100857 ∧ x1 = 786432*q+302572 ∧ x2 = 393216*q+151286 ∧ x3 = 196608*q+75643 ∧ x4 = 589824*q+226930 ∧ x5 = 294912*q+113465 ∧ x6 = 884736*q+340396 ∧ x7 = 442368*q+170198 ∧ x8 = 221184*q+85099 ∧ x9 = 663552*q+255298 ∧ x10 = 331776*q+127649 ∧ x11 = 995328*q+382948 ∧ x12 = 497664*q+191474 ∧ x13 = 248832*q+95737 ∧ x14 = 746496*q+287212 ∧ x15 = 373248*q+143606 ∧ x16 = 186624*q+71803 ∧ x17 = 559872*q+215410 ∧ x18 = 279936*q+107705 ∧ x19 = 839808*q+323116 ∧ x20 = 419904*q+161558 ∧ x21 = 209952*q+80779 ∧ x22 = 629856*q+242338 ∧ x23 = 314928*q+121169 ∧ x24 = 944784*q+363508 ∧ x25 = 472392*q+181754 ∧ x26 = 236196*q+90877 ∧ x27 = 708588*q+272632 ∧ x28 = 354294*q+136316 ∧ x29 = 177147*q+68158 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28⟩ := parameters_1001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hstep := r28.1
  have hparity := r28.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p28 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27
    omega

/-- Exact source residue and full affine trace for branch `10010100101001001010010100101`. -/
theorem parameters_10010100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : Nat)
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
    (r22 : (2*x23 = x22 ∧ x22%2 = 0))
    (r23 : (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0))
    (r28 : (x29 = 3*x28+1 ∧ x28%2 = 1))
    : ∃ q : Nat, x0 = 262144*q+231929 ∧ x1 = 786432*q+695788 ∧ x2 = 393216*q+347894 ∧ x3 = 196608*q+173947 ∧ x4 = 589824*q+521842 ∧ x5 = 294912*q+260921 ∧ x6 = 884736*q+782764 ∧ x7 = 442368*q+391382 ∧ x8 = 221184*q+195691 ∧ x9 = 663552*q+587074 ∧ x10 = 331776*q+293537 ∧ x11 = 995328*q+880612 ∧ x12 = 497664*q+440306 ∧ x13 = 248832*q+220153 ∧ x14 = 746496*q+660460 ∧ x15 = 373248*q+330230 ∧ x16 = 186624*q+165115 ∧ x17 = 559872*q+495346 ∧ x18 = 279936*q+247673 ∧ x19 = 839808*q+743020 ∧ x20 = 419904*q+371510 ∧ x21 = 209952*q+185755 ∧ x22 = 629856*q+557266 ∧ x23 = 314928*q+278633 ∧ x24 = 944784*q+835900 ∧ x25 = 472392*q+417950 ∧ x26 = 236196*q+208975 ∧ x27 = 708588*q+626926 ∧ x28 = 354294*q+313463 ∧ x29 = 1062882*q+940390 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28⟩ := parameters_1001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
  have hstep := r28.1
  have hparity := r28.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p28 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27
    omega

/-- Exact source residue and full affine trace for branch `010010100101001001010010100100`. -/
theorem parameters_010010100101001001010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0))
    (r29 : (2*x30 = x29 ∧ x29%2 = 0))
    : ∃ q : Nat, x0 = 524288*q+201714 ∧ x1 = 262144*q+100857 ∧ x2 = 786432*q+302572 ∧ x3 = 393216*q+151286 ∧ x4 = 196608*q+75643 ∧ x5 = 589824*q+226930 ∧ x6 = 294912*q+113465 ∧ x7 = 884736*q+340396 ∧ x8 = 442368*q+170198 ∧ x9 = 221184*q+85099 ∧ x10 = 663552*q+255298 ∧ x11 = 331776*q+127649 ∧ x12 = 995328*q+382948 ∧ x13 = 497664*q+191474 ∧ x14 = 248832*q+95737 ∧ x15 = 746496*q+287212 ∧ x16 = 373248*q+143606 ∧ x17 = 186624*q+71803 ∧ x18 = 559872*q+215410 ∧ x19 = 279936*q+107705 ∧ x20 = 839808*q+323116 ∧ x21 = 419904*q+161558 ∧ x22 = 209952*q+80779 ∧ x23 = 629856*q+242338 ∧ x24 = 314928*q+121169 ∧ x25 = 944784*q+363508 ∧ x26 = 472392*q+181754 ∧ x27 = 236196*q+90877 ∧ x28 = 708588*q+272632 ∧ x29 = 354294*q+136316 ∧ x30 = 177147*q+68158 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29⟩ := parameters_01001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  have hstep := r29.1
  have hparity := r29.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
  have hq : q = 2*(q/2)+0 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p28 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p29 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
    omega

/-- Exact source residue and full affine trace for branch `010010100101001001010010100101`. -/
theorem parameters_010010100101001001010010100101
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : Nat)
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
    (r22 : (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0))
    (r24 : (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0))
    (r27 : (x28 = 3*x27+1 ∧ x27%2 = 1))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0))
    (r29 : (x30 = 3*x29+1 ∧ x29%2 = 1))
    : ∃ q : Nat, x0 = 524288*q+463858 ∧ x1 = 262144*q+231929 ∧ x2 = 786432*q+695788 ∧ x3 = 393216*q+347894 ∧ x4 = 196608*q+173947 ∧ x5 = 589824*q+521842 ∧ x6 = 294912*q+260921 ∧ x7 = 884736*q+782764 ∧ x8 = 442368*q+391382 ∧ x9 = 221184*q+195691 ∧ x10 = 663552*q+587074 ∧ x11 = 331776*q+293537 ∧ x12 = 995328*q+880612 ∧ x13 = 497664*q+440306 ∧ x14 = 248832*q+220153 ∧ x15 = 746496*q+660460 ∧ x16 = 373248*q+330230 ∧ x17 = 186624*q+165115 ∧ x18 = 559872*q+495346 ∧ x19 = 279936*q+247673 ∧ x20 = 839808*q+743020 ∧ x21 = 419904*q+371510 ∧ x22 = 209952*q+185755 ∧ x23 = 629856*q+557266 ∧ x24 = 314928*q+278633 ∧ x25 = 944784*q+835900 ∧ x26 = 472392*q+417950 ∧ x27 = 236196*q+208975 ∧ x28 = 708588*q+626926 ∧ x29 = 354294*q+313463 ∧ x30 = 1062882*q+940390 := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29⟩ := parameters_01001010010100100101001010010 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
  have hstep := r29.1
  have hparity := r29.2
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
  have hq : q = 2*(q/2)+1 := by
    clear hstep p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
    omega
  clear hparity
  refine ⟨q/2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p23 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p24 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p25 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p26 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p27 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p28 hq
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using lift_affine p29 hq
  · clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28
    omega

/-- Terminal branch `000` cannot satisfy the band bounds. -/
theorem exclude_000
    (x0 x1 x2 x3 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3⟩ := parameters_000 x0 x1 x2 x3 r0 r1 r2
  clear r0 r1 r2
  clear p1 p2
  omega

/-- Terminal branch `001000` cannot satisfy the band bounds. -/
theorem exclude_001000
    (x0 x1 x2 x3 x4 x5 x6 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h6 : b ≤ x6 ∧ 2*x6 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6⟩ := parameters_001000 x0 x1 x2 x3 x4 x5 x6 r0 r1 r2 r3 r4 r5
  clear r0 r1 r2 r3 r4 r5
  clear p1 p2 p3 p4 p5
  omega

/-- Terminal branch `00100100` cannot satisfy the band bounds. -/
theorem exclude_00100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h8 : b ≤ x8 ∧ 2*x8 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8⟩ := parameters_00100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 r0 r1 r2 r3 r4 r5 r6 r7
  clear r0 r1 r2 r3 r4 r5 r6 r7
  clear p1 p2 p3 p4 p5 p6 p7
  omega

/-- Terminal branch `00100101000` cannot satisfy the band bounds. -/
theorem exclude_00100101000
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h11 : b ≤ x11 ∧ 2*x11 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0))
    (r2 : (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0))
    (r5 : (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0))
    (r7 : (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0))
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11⟩ := parameters_00100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  omega

/-- Terminal branch `0010010100100` cannot satisfy the band bounds. -/
theorem exclude_0010010100100
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Nat)
    (b : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h13 : b ≤ x13 ∧ 2*x13 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0))
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
    : False := by
  obtain ⟨q,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13⟩ := parameters_0010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
  omega


end Collatz.Exploration.ElevenHalvesArithmetic
