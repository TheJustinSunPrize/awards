import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step114918 (p2192 p2210 p2761 p3425 p3434 p3461 p4393 p4733 p5254 : Prop)
    (h105430 : p4733)
    (h96112 : (¬ p4393) ∨ (¬ p3434) ∨ p2192 ∨ p2210 ∨ p3425 ∨ (¬ p4733) ∨ (¬ p2761) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3434) ∨ p2210 ∨ p3425 ∨ (¬ p2761) ∨ (¬ p4393) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : (¬ p5254) := (Or.elim h96112 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => r6))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114919 (p2132 p2449 p2761 p2807 p2860 p3461 p4393 p4786 p5254 : Prop)
    (h106425 : p4786)
    (h96122 : (¬ p4393) ∨ p2132 ∨ p2860 ∨ (¬ p4786) ∨ (¬ p2807) ∨ (¬ p2761) ∨ (¬ p2449) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2132 ∨ p2860 ∨ (¬ p4393) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5254) := (Or.elim h96122 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => r6))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114920 (p2132 p2860 p3166 p3256 p3266 p3461 p4393 p4786 p5254 : Prop)
    (h106425 : p4786)
    (h96125 : (¬ p4393) ∨ (¬ p3166) ∨ p2860 ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p3256) ∨ (¬ p4786) ∨ p2132)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p3256) ∨ p2860 ∨ p2132 ∨ (¬ p3166) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5254) := (Or.elim h96125 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114921 (p2241 p2707 p2750 p2761 p3093 p3434 p3461 p4435 p5254 : Prop)
    (h106345 : p2750)
    (h96696 : (¬ p4435) ∨ (¬ p2241) ∨ (¬ p2750) ∨ p3093 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p5254) ∨ (¬ p2761))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4435) ∨ (¬ p2761) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p2241) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : (¬ p5254) := (Or.elim h96696 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114922 (p2254 p2651 p2761 p3016 p3399 p3461 p3631 p5254 p5514 : Prop)
    (h105366 : p2254)
    (h99895 : (¬ p3631) ∨ (¬ p5514) ∨ (¬ p5254) ∨ (¬ p2254) ∨ (¬ p3399) ∨ p3016 ∨ (¬ p2761) ∨ p2651)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3399) ∨ p3016 ∨ (¬ p2761) ∨ (¬ p3631) ∨ (¬ p5514) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : (¬ p5254) := (Or.elim h99895 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114923 (p2449 p2598 p2761 p2807 p3422 p3461 p4786 p5254 p5514 : Prop)
    (h106425 : p4786)
    (h99898 : (¬ p5514) ∨ p3422 ∨ (¬ p4786) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p5254) ∨ (¬ p2761) ∨ p2598)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ (¬ p2807) ∨ p3422 ∨ (¬ p2761) ∨ (¬ p2449) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5254) := (Or.elim h99898 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114924 (p2598 p2761 p3399 p3422 p3461 p3631 p4736 p5254 p5514 : Prop)
    (h105431 : p4736)
    (h99899 : (¬ p5514) ∨ p3422 ∨ (¬ p4736) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p2761) ∨ (¬ p5254) ∨ p2598)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ p3422 ∨ (¬ p3399) ∨ (¬ p2761) ∨ (¬ p3631) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : (¬ p5254) := (Or.elim h99899 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114925 (p2139 p2220 p2598 p3146 p3266 p3422 p3461 p5254 p5514 : Prop)
    (h101461 : (¬ p5514) ∨ p3422 ∨ p2598 ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p5254) ∨ (¬ p2220) ∨ (¬ p2139))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p3422 ∨ (¬ p3266) ∨ p2598 ∨ (¬ p5514) ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5254) := (Or.elim h101461 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114926 (p2651 p2761 p3016 p3425 p3434 p3461 p4789 p5254 p5514 : Prop)
    (h105646 : p4789)
    (h101762 : (¬ p5514) ∨ (¬ p2761) ∨ p3016 ∨ (¬ p5254) ∨ p2651 ∨ (¬ p3434) ∨ p3425 ∨ (¬ p4789))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ p3016 ∨ p3425 ∨ (¬ p2761) ∨ (¬ p3434) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    let u8 : (¬ p5254) := (Or.elim h101762 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114928 (p2241 p2641 p2761 p3051 p3246 p3461 p4228 p4521 p5254 : Prop)
    (h110229 : p4228 ∨ (¬ p5254) ∨ (¬ p3246) ∨ (¬ p3051) ∨ p2241 ∨ p2641 ∨ (¬ p4521) ∨ (¬ p2761))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ (¬ p3246) ∨ (¬ p3051) ∨ p2241 ∨ p2641 ∨ (¬ p4521) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5254) := (Or.elim h110229 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114929 (p2696 p2761 p2797 p3073 p3449 p3461 p4228 p4445 p5254 : Prop)
    (h110232 : p4228 ∨ (¬ p5254) ∨ (¬ p2761) ∨ (¬ p3449) ∨ p2797 ∨ (¬ p4445) ∨ p2696 ∨ (¬ p3073))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ (¬ p2761) ∨ (¬ p3449) ∨ p2797 ∨ (¬ p4445) ∨ p2696 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5254) := (Or.elim h110232 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114942 (p2252 p2284 p2608 p2750 p2946 p3461 p3707 p3830 p4393 p5254 : Prop)
    (h106345 : p2750)
    (h96113 : (¬ p4393) ∨ (¬ p3830) ∨ (¬ p5254) ∨ (¬ p3707) ∨ (¬ p2252) ∨ p2284 ∨ p2946 ∨ p2608 ∨ (¬ p2750))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ p2284 ∨ (¬ p3830) ∨ (¬ p3707) ∨ (¬ p2252) ∨ p2608 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : (¬ p5254) := (Or.elim h96113 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114951 (p2417 p2696 p2761 p2797 p3366 p3389 p3461 p3519 p4228 p5254 : Prop)
    (h110233 : p4228 ∨ (¬ p2417) ∨ (¬ p3519) ∨ p2797 ∨ (¬ p2761) ∨ p2696 ∨ (¬ p3389) ∨ (¬ p3366) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ (¬ p2417) ∨ (¬ p3519) ∨ p2797 ∨ (¬ p2761) ∨ p2696 ∨ (¬ p3389) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5254) := (Or.elim h110233 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => r7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114952 (p2470 p2528 p2696 p2797 p3266 p3366 p3461 p3519 p4228 p5254 : Prop)
    (h110234 : p4228 ∨ (¬ p5254) ∨ p2797 ∨ (¬ p2470) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p2528))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ p2797 ∨ (¬ p2470) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5254) := (Or.elim h110234 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114954 (p2696 p2761 p2797 p3051 p3246 p3366 p3370 p3461 p4228 p5254 : Prop)
    (h110236 : p4228 ∨ (¬ p2761) ∨ (¬ p3051) ∨ p2696 ∨ p2797 ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ (¬ p2761) ∨ (¬ p3051) ∨ p2696 ∨ p2797 ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5254) := (Or.elim h110236 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => r7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114956 (p2417 p2608 p2761 p2829 p3093 p3389 p3461 p3519 p4329 p5254 : Prop)
    (h113657 : p2829 ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4329) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p2829 ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4329) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5254) := (Or.elim h113657 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => r7))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114957 (p2341 p2608 p2881 p3093 p3146 p3266 p3461 p3543 p4435 p5254 : Prop)
    (h114510 : p2881 ∨ (¬ p4435) ∨ (¬ p5254) ∨ (¬ p3146) ∨ p3093 ∨ (¬ p3266) ∨ (¬ p3543) ∨ (¬ p2341) ∨ (¬ p2608))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p2881 ∨ (¬ p4435) ∨ (¬ p3146) ∨ p3093 ∨ (¬ p3266) ∨ (¬ p3543) ∨ (¬ p2341) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5254) := (Or.elim h114510 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114972 (p2284 p2761 p2946 p3361 p3425 p3434 p3461 p3619 p4393 p4778 p5254 : Prop)
    (h109615 : (¬ p3434) ∨ (¬ p5254) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p3361) ∨ (¬ p3619) ∨ (¬ p4393) ∨ p2946 ∨ p2284 ∨ (¬ p4778))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3434) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p3361) ∨ (¬ p3619) ∨ (¬ p4393) ∨ p2946 ∨ p2284 ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5254) := (Or.elim h109615 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114977 (p2246 p2341 p2459 p2498 p2608 p2744 p3093 p3266 p3461 p4104 p5254 p5514 : Prop)
    (h106503 : p2744)
    (h89695 : p3093 ∨ (¬ p2246) ∨ (¬ p5514) ∨ (¬ p2498) ∨ (¬ p2341) ∨ (¬ p2744) ∨ (¬ p5254) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p3266) ∨ (¬ p4104))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ (¬ p3266) ∨ (¬ p2341) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p2246) ∨ (¬ p2498) ∨ (¬ p4104) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : (¬ p5254) := (Or.elim h89695 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u8))))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114979 (p2651 p2761 p3016 p3051 p3246 p3366 p3370 p3461 p4236 p4377 p5254 p5514 : Prop)
    (h106170 : p4377)
    (h94702 : (¬ p3370) ∨ (¬ p5514) ∨ (¬ p5254) ∨ p2651 ∨ (¬ p3246) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3051) ∨ (¬ p2761) ∨ p3016 ∨ (¬ p4236))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ (¬ p3246) ∨ p3016 ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3370) ∨ p2651 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4377 := h106170;
    let u11 : (¬ p5254) := (Or.elim h94702 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114980 (p2230 p2241 p2744 p2860 p3366 p3461 p3695 p3707 p3830 p3905 p4393 p5254 : Prop)
    (h106503 : p2744)
    (h94715 : (¬ p4393) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3695) ∨ (¬ p3830) ∨ p2230 ∨ (¬ p3366) ∨ p2860 ∨ (¬ p3905) ∨ (¬ p5254) ∨ (¬ p3707))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ p2860 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2230 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : (¬ p5254) := (Or.elim h94715 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (r9 u5))))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114981 (p2341 p2528 p2608 p3093 p3266 p3461 p3519 p4376 p4383 p4435 p5201 p5254 : Prop)
    (h106320 : p4376)
    (h96705 : (¬ p4435) ∨ (¬ p2341) ∨ p3093 ∨ (¬ p3519) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p4383) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p5201) ∨ (¬ p2528))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4435) ∨ (¬ p2528) ∨ p3093 ∨ (¬ p3266) ∨ (¬ p3519) ∨ (¬ p4383) ∨ (¬ p5201) ∨ (¬ p2341) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    let u11 : (¬ p5254) := (Or.elim h96705 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u2))))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114983 (p2341 p2696 p2797 p2881 p3146 p3266 p3366 p3370 p3461 p4228 p4988 p5254 : Prop)
    (h114513 : p2881 ∨ p4228 ∨ (¬ p3146) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p4988) ∨ p2696)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p2881 ∨ p4228 ∨ (¬ p3146) ∨ p2797 ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p4988) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4228) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p5254) := (Or.elim h114513 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (u10 r9))))))))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114987 (p2417 p2427 p3246 p3569 : Prop)
    (h34724 : p2417 ∨ (¬ p3246) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3246) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3569) := (Or.elim h34724 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h82329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114988 (p2427 p3569 p3579 p4333 : Prop)
    (h25208 : (¬ p3569) ∨ (¬ p3579) ∨ p4333)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p4333 ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4333) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3569) := (Or.elim h25208 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h82329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114989 (p2427 p2881 p2911 p3569 : Prop)
    (h100184 : (¬ p3569) ∨ p2911 ∨ (¬ p2881))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2881) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3569) := (Or.elim h100184 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h82329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114990 (p2427 p3201 p3569 p4344 : Prop)
    (h113433 : (¬ p3201) ∨ p4344 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3201) ∨ p4344 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4344) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3569) := (Or.elim h113433 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h82329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114991 (p2427 p2922 p3569 p3571 : Prop)
    (h114241 : (¬ p2922) ∨ p3571 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2922) ∨ p3571 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3571) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3569) := (Or.elim h114241 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h82329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114993 (p2427 p2922 p3051 p3379 p3569 : Prop)
    (h88748 : p3051 ∨ (¬ p3379) ∨ (¬ p3569) ∨ (¬ p2922))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3379) ∨ p3051 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3569) := (Or.elim h88748 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114997 (p2427 p2881 p2922 p3527 p3569 : Prop)
    (h114245 : (¬ p2922) ∨ (¬ p2881) ∨ p3527 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2922) ∨ (¬ p2881) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3569) := (Or.elim h114245 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h82329 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114999 (p2230 p2427 p2440 p2881 p3389 p3569 : Prop)
    (h74536 : (¬ p3389) ∨ p2440 ∨ (¬ p3569) ∨ (¬ p2881) ∨ p2230)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2881) ∨ p2440 ∨ (¬ p3389) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h74536 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115000 (p2230 p2427 p2440 p3246 p3389 p3569 : Prop)
    (h74661 : (¬ p3246) ∨ p2440 ∨ (¬ p3389) ∨ (¬ p3569) ∨ p2230)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3389) ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h74661 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115001 (p2230 p2427 p2901 p3389 p3569 p4702 : Prop)
    (h106079 : p4702)
    (h74663 : p2901 ∨ (¬ p3389) ∨ p2230 ∨ (¬ p4702) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2901 ∨ (¬ p3389) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    let u5 : (¬ p3569) := (Or.elim h74663 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115003 (p2230 p2406 p2427 p2881 p3389 p3569 : Prop)
    (h74665 : (¬ p3389) ∨ (¬ p3569) ∨ p2230 ∨ (¬ p2406) ∨ (¬ p2881))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p2406) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h74665 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115005 (p2230 p2427 p2563 p3389 p3569 p4558 : Prop)
    (h105400 : p4558)
    (h74773 : (¬ p3389) ∨ p2563 ∨ (¬ p3569) ∨ p2230 ∨ (¬ p4558))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2563 ∨ (¬ p3389) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    let u5 : (¬ p3569) := (Or.elim h74773 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115006 (p2427 p2850 p2901 p3201 p3569 p4702 : Prop)
    (h106079 : p4702)
    (h77080 : p2901 ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p4702) ∨ p2850)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2901 ∨ (¬ p3201) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    let u5 : (¬ p3569) := (Or.elim h77080 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115007 (p2427 p2850 p3051 p3201 p3569 p4533 : Prop)
    (h105394 : p4533)
    (h77083 : p3051 ∨ (¬ p3201) ∨ (¬ p3569) ∨ p2850 ∨ (¬ p4533))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3201) ∨ p3051 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    let u5 : (¬ p3569) := (Or.elim h77083 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115008 (p2230 p2427 p2850 p3201 p3246 p3569 : Prop)
    (h77087 : (¬ p3201) ∨ p2850 ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p2230) ∨ p2850 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h77087 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115015 (p2406 p2427 p2870 p2922 p3569 p4882 : Prop)
    (h105453 : p4882)
    (h86685 : (¬ p2922) ∨ p2870 ∨ (¬ p4882) ∨ p2406 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2870 ∨ (¬ p2922) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    let u5 : (¬ p3569) := (Or.elim h86685 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115018 (p2406 p2427 p2922 p3051 p3569 p4533 : Prop)
    (h105394 : p4533)
    (h88740 : (¬ p2922) ∨ p3051 ∨ p2406 ∨ (¬ p4533) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2922) ∨ p2406 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    let u5 : (¬ p3569) := (Or.elim h88740 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115020 (p2406 p2427 p2563 p2922 p3569 p4558 : Prop)
    (h105400 : p4558)
    (h88863 : (¬ p2922) ∨ (¬ p3569) ∨ p2563 ∨ (¬ p4558) ∨ p2406)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2563 ∨ (¬ p2922) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    let u5 : (¬ p3569) := (Or.elim h88863 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115021 (p2427 p2437 p2440 p2891 p3569 p4629 : Prop)
    (h92723 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4629) ∨ p2891 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2891 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h92723 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115022 (p2427 p2437 p2440 p2563 p3569 p4558 : Prop)
    (h105400 : p4558)
    (h98028 : (¬ p2440) ∨ (¬ p4558) ∨ p2563 ∨ (¬ p2437) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2440) ∨ (¬ p2437) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    let u5 : (¬ p3569) := (Or.elim h98028 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115023 (p2406 p2427 p2922 p2982 p3246 p3569 : Prop)
    (h108331 : p3246 ∨ p2982 ∨ (¬ p2922) ∨ p2406 ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p3246 ∨ p2982 ∨ (¬ p2922) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h108331 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115024 (p2373 p2406 p2427 p2881 p2922 p3569 : Prop)
    (h109421 : p2881 ∨ p2373 ∨ p2406 ∨ (¬ p3569) ∨ (¬ p2922))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2881 ∨ p2373 ∨ p2406 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3569) := (Or.elim h109421 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115025 (p2406 p2427 p2901 p3389 p3519 p3569 p4702 : Prop)
    (h106079 : p4702)
    (h76860 : (¬ p3519) ∨ p2901 ∨ (¬ p3569) ∨ (¬ p3389) ∨ (¬ p4702) ∨ p2406)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2901 ∨ (¬ p3389) ∨ p2406 ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    let u6 : (¬ p3569) := (Or.elim h76860 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115026 (p2156 p2427 p2850 p3201 p3569 p4031 p4558 : Prop)
    (h105400 : p4558)
    (h77085 : (¬ p4031) ∨ p2850 ∨ (¬ p4558) ∨ (¬ p3569) ∨ (¬ p3201) ∨ p2156)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2156 ∨ (¬ p4031) ∨ (¬ p3201) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p3569) := (Or.elim h77085 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115028 (p2284 p2417 p2427 p2449 p2995 p3569 p4558 : Prop)
    (h105400 : p4558)
    (h86532 : p2417 ∨ (¬ p2449) ∨ (¬ p3569) ∨ (¬ p2995) ∨ (¬ p4558) ∨ p2284)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2449) ∨ p2417 ∨ (¬ p2995) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p3569) := (Or.elim h86532 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115032 (p2230 p2427 p2563 p2922 p3347 p3569 p4558 : Prop)
    (h105400 : p4558)
    (h88842 : (¬ p2922) ∨ (¬ p4558) ∨ p2230 ∨ (¬ p3347) ∨ (¬ p3569) ∨ p2563)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2563 ∨ (¬ p2922) ∨ (¬ p3347) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p3569) := (Or.elim h88842 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115033 (p2427 p2437 p2663 p2881 p3343 p3355 p3569 : Prop)
    (h89498 : (¬ p3355) ∨ p3343 ∨ (¬ p2663) ∨ (¬ p2437) ∨ (¬ p3569) ∨ (¬ p2881))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p3343 ∨ (¬ p2881) ∨ (¬ p3355) ∨ (¬ p2437) ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3569) := (Or.elim h89498 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115035 (p2156 p2192 p2427 p2891 p3569 p3741 p4533 : Prop)
    (h105394 : p4533)
    (h92673 : (¬ p2192) ∨ p2156 ∨ (¬ p3569) ∨ p2891 ∨ (¬ p3741) ∨ (¬ p4533))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2891 ∨ p2156 ∨ (¬ p2192) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4533 := h105394;
    let u6 : (¬ p3569) := (Or.elim h92673 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115037 (p2230 p2427 p2891 p3389 p3569 p4243 p4882 : Prop)
    (h105453 : p4882)
    (h92978 : (¬ p4243) ∨ (¬ p4882) ∨ (¬ p3389) ∨ p2891 ∨ (¬ p3569) ∨ p2230)
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2891 ∨ (¬ p3389) ∨ (¬ p4243) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    let u6 : (¬ p3569) := (Or.elim h92978 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115040 (p2427 p3201 p3422 p3569 p4140 p5472 p5514 : Prop)
    (h100193 : (¬ p3201) ∨ (¬ p5514) ∨ p3422 ∨ (¬ p4140) ∨ (¬ p3569) ∨ (¬ p5472))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p5514) ∨ (¬ p5472) ∨ (¬ p4140) ∨ (¬ p3201) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3569) := (Or.elim h100193 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115066 (p2331 p2341 p2427 p2449 p2797 p2911 p3246 p3366 p3519 p3569 p3755 p4236 p4399 p4988 : Prop)
    (h109329 : (¬ p2449) ∨ (¬ p2797) ∨ p3755 ∨ (¬ p4236) ∨ (¬ p3246) ∨ p2911 ∨ (¬ p3366) ∨ p2331 ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2341) ∨ (¬ p4988) ∨ (¬ p3569))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2449) ∨ (¬ p2797) ∨ p3755 ∨ (¬ p4236) ∨ (¬ p3246) ∨ p2911 ∨ (¬ p3366) ∨ p2331 ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2341) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p3569) := (Or.elim h109329 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => r11))))))))))))))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115068 (p2341 p2427 p2911 p3246 p3286 p3366 p3461 p3519 p3569 p4236 p4376 p4399 p4625 p4988 p5284 : Prop)
    (h106320 : p4376)
    (h106455 : p4625)
    (h100312 : (¬ p5284) ∨ (¬ p2341) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p4988) ∨ p2911 ∨ p3286 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3246) ∨ (¬ p4399) ∨ (¬ p4625) ∨ (¬ p3366))
    (h82329 : p3569 ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p3461) ∨ p3286 ∨ (¬ p3246) ∨ p2911 ∨ (¬ p3366) ∨ (¬ p5284) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p4988) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4376 := h106320;
    let u13 : p4625 := h106455;
    let u14 : (¬ p3569) := (Or.elim h100312 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u9))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u13))) (fun r12 => (False.elim (r12 u5))))))))))))))))))))))))))));
    (Or.elim h82329 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115069 (p2406 p2850 p3590 p3698 : Prop)
    (h111155 : p2850 ∨ (¬ p2406) ∨ (¬ p3698) ∨ (¬ p3590))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2406) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3698) := (Or.elim h111155 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115072 (p2427 p2850 p2870 p3698 : Prop)
    (h90155 : (¬ p2870) ∨ p2427 ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2427 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3698) := (Or.elim h90155 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115073 (p2563 p2850 p2860 p3698 : Prop)
    (h90162 : (¬ p3698) ∨ (¬ p2860) ∨ p2563)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2860) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3698) := (Or.elim h90162 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115074 (p2850 p2982 p3105 p3698 : Prop)
    (h24465 : p2982 ∨ (¬ p3105) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2982 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3698) := (Or.elim h24465 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115075 (p2373 p2619 p2850 p3698 : Prop)
    (h90186 : (¬ p2619) ∨ p2373 ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2373 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3698) := (Or.elim h90186 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115077 (p2427 p2850 p2891 p3698 p4418 : Prop)
    (h80762 : (¬ p2891) ∨ (¬ p4418) ∨ p2427 ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2427 ∨ (¬ p2891) ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3698) := (Or.elim h80762 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => r2))))));
    (Or.elim h102190 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115078 (p2137 p2427 p2850 p3051 p3698 : Prop)
    (h90157 : (¬ p3051) ∨ p2427 ∨ (¬ p3698) ∨ (¬ p2137))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2427 ∨ (¬ p3051) ∨ (¬ p2137) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3698) := (Or.elim h90157 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115079 (p2406 p2839 p2850 p3541 p3698 : Prop)
    (h90168 : p2839 ∨ (¬ p3541) ∨ (¬ p2406) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2406) ∨ (¬ p3541) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3698) := (Or.elim h90168 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h102190 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115080 (p2850 p2870 p2982 p3698 p4192 : Prop)
    (h90173 : (¬ p4192) ∨ p2982 ∨ (¬ p2870) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p4192) ∨ p2982 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3698) := (Or.elim h90173 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h102190 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115084 (p2132 p2598 p2850 p3201 p3698 p4646 : Prop)
    (h105534 : p4646)
    (h77073 : (¬ p3201) ∨ p2132 ∨ (¬ p4646) ∨ (¬ p2598) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ (¬ p3201) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    let u5 : (¬ p3698) := (Or.elim h77073 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115085 (p2839 p2850 p3201 p3367 p3698 p4646 : Prop)
    (h105534 : p4646)
    (h77136 : (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3698) ∨ (¬ p4646) ∨ p2839)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3367) ∨ p2839 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    let u5 : (¬ p3698) := (Or.elim h77136 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115086 (p2132 p2598 p2850 p3641 p3698 p4610 : Prop)
    (h77406 : p2132 ∨ (¬ p3641) ∨ (¬ p4610) ∨ (¬ p3698) ∨ (¬ p2598))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4610) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h77406 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115087 (p2839 p2850 p3367 p3422 p3698 p4717 : Prop)
    (h105424 : p4717)
    (h77706 : (¬ p3367) ∨ p2839 ∨ (¬ p3422) ∨ (¬ p3698) ∨ (¬ p4717))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2839 ∨ (¬ p3422) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p3698) := (Or.elim h77706 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115088 (p2187 p2563 p2839 p2850 p3367 p3698 : Prop)
    (h78019 : (¬ p3367) ∨ p2839 ∨ p2563 ∨ (¬ p3698) ∨ p2187)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2187 ∨ p2839 ∨ (¬ p3367) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h78019 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115091 (p2440 p2707 p2839 p2850 p3425 p3698 : Prop)
    (h88678 : (¬ p2707) ∨ p2839 ∨ (¬ p3425) ∨ (¬ p3698) ∨ p2440)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2707) ∨ (¬ p3425) ∨ p2839 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h88678 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115092 (p2132 p2440 p2598 p2850 p3698 p4750 : Prop)
    (h105433 : p4750)
    (h90089 : p2132 ∨ p2440 ∨ (¬ p3698) ∨ (¬ p4750) ∨ (¬ p2598))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ p2440 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p3698) := (Or.elim h90089 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115093 (p2132 p2427 p2598 p2850 p3367 p3698 : Prop)
    (h90160 : p2132 ∨ (¬ p3698) ∨ p3367 ∨ (¬ p2598) ∨ p2427)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ p2427 ∨ p3367 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h90160 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115094 (p2563 p2598 p2839 p2850 p3367 p3698 : Prop)
    (h90164 : (¬ p3698) ∨ (¬ p3367) ∨ p2563 ∨ p2598 ∨ p2839)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2563 ∨ (¬ p3367) ∨ p2839 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h90164 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115095 (p2132 p2406 p2598 p2850 p3698 p5217 : Prop)
    (h105493 : p5217)
    (h90165 : p2132 ∨ (¬ p2406) ∨ (¬ p5217) ∨ (¬ p2598) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ (¬ p2406) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    let u5 : (¬ p3698) := (Or.elim h90165 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115097 (p2440 p2839 p2850 p3367 p3698 p4750 : Prop)
    (h105433 : p4750)
    (h90167 : (¬ p3367) ∨ p2839 ∨ p2440 ∨ (¬ p3698) ∨ (¬ p4750))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2839 ∨ (¬ p3367) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p3698) := (Or.elim h90167 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115098 (p2230 p2839 p2850 p3367 p3698 p4730 : Prop)
    (h106074 : p4730)
    (h90169 : (¬ p3698) ∨ (¬ p3367) ∨ p2839 ∨ (¬ p4730) ∨ (¬ p2230))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2839 ∨ (¬ p2230) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p3698) := (Or.elim h90169 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115100 (p2274 p2563 p2839 p2850 p3367 p3698 : Prop)
    (h90177 : (¬ p3367) ∨ p2839 ∨ p2274 ∨ p2563 ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2274 ∨ p2563 ∨ (¬ p3367) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h90177 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115102 (p2132 p2406 p2850 p3379 p3698 p4736 : Prop)
    (h105431 : p4736)
    (h90989 : (¬ p2406) ∨ (¬ p4736) ∨ (¬ p3698) ∨ p2132 ∨ (¬ p3379))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3379) ∨ p2132 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4736 := h105431;
    let u5 : (¬ p3698) := (Or.elim h90989 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115105 (p2839 p2850 p3333 p3367 p3698 p4953 : Prop)
    (h95603 : (¬ p3333) ∨ p2839 ∨ (¬ p3367) ∨ (¬ p3698) ∨ (¬ p4953))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p4953) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h95603 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115106 (p2440 p2819 p2829 p2839 p2850 p3698 : Prop)
    (h99671 : (¬ p2829) ∨ (¬ p2819) ∨ p2440 ∨ (¬ p3698) ∨ p2839)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2819) ∨ (¬ p2829) ∨ p2440 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3698) := (Or.elim h99671 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115112 (p2470 p2839 p2850 p3367 p3698 p3759 p4610 : Prop)
    (h90059 : (¬ p3367) ∨ p2839 ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p2470) ∨ (¬ p4610))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2470) ∨ p2839 ∨ (¬ p4610) ∨ (¬ p3759) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3698) := (Or.elim h90059 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115113 (p2373 p2598 p2839 p2850 p3367 p3698 p3873 : Prop)
    (h90170 : (¬ p3367) ∨ p2839 ∨ p2598 ∨ (¬ p3873) ∨ (¬ p3698) ∨ p2373)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3873) ∨ (¬ p3367) ∨ p2839 ∨ p2373 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3698) := (Or.elim h90170 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115114 (p2839 p2850 p3367 p3389 p3698 p3759 p4646 : Prop)
    (h105534 : p4646)
    (h90175 : p2839 ∨ (¬ p3367) ∨ (¬ p4646) ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2839 ∨ (¬ p3759) ∨ (¬ p3367) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4646 := h105534;
    let u6 : (¬ p3698) := (Or.elim h90175 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115119 (p2132 p2598 p2850 p2922 p3590 p3698 p4646 : Prop)
    (h105534 : p4646)
    (h90196 : p2132 ∨ (¬ p3590) ∨ (¬ p2598) ∨ (¬ p3698) ∨ (¬ p4646) ∨ (¬ p2922))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2598) ∨ (¬ p2922) ∨ p2132 ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4646 := h105534;
    let u6 : (¬ p3698) := (Or.elim h90196 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115121 (p2761 p2850 p2870 p2982 p3246 p3698 p4129 : Prop)
    (h112309 : p3246 ∨ (¬ p2761) ∨ (¬ p4129) ∨ p2982 ∨ (¬ p3698) ∨ (¬ p2870))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p3246 ∨ (¬ p2761) ∨ (¬ p4129) ∨ p2982 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3698) := (Or.elim h112309 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115129 (p2137 p2440 p2850 p2901 p3051 p3083 p3698 p4610 : Prop)
    (h114893 : (¬ p2440) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p3083) ∨ (¬ p4610) ∨ (¬ p2137) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p2440) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p3083) ∨ (¬ p4610) ∨ (¬ p2137) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3698) := (Or.elim h114893 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115133 (p2363 p2563 p2598 p2619 p2850 p2911 p3146 p3201 p3698 p4133 : Prop)
    (h105712 : p4133)
    (h78808 : (¬ p2619) ∨ p3201 ∨ (¬ p4133) ∨ p2363 ∨ (¬ p3146) ∨ (¬ p3698) ∨ p2598 ∨ p2563 ∨ p2911)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2363 ∨ (¬ p2619) ∨ p2563 ∨ p2598 ∨ (¬ p3146) ∨ p2911 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : (¬ p3698) := (Or.elim h78808 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u6 r7))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115136 (p2230 p2331 p2850 p2870 p3323 p3362 p3461 p3698 p4129 p4789 p4826 : Prop)
    (h105444 : p4826)
    (h105646 : p4789)
    (h80302 : (¬ p4129) ∨ p2331 ∨ (¬ p4789) ∨ (¬ p2870) ∨ p3461 ∨ (¬ p4826) ∨ (¬ p3362) ∨ p3323 ∨ (¬ p2230) ∨ (¬ p3698))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p3323 ∨ p3461 ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2870) ∨ (¬ p3362) ∨ (¬ p4129) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4826 := h105444;
    let u9 : p4789 := h105646;
    let u10 : (¬ p3698) := (Or.elim h80302 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => r8))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115138 (p2230 p2331 p2668 p2850 p3105 p3362 p3680 p3698 p4789 p5123 p5580 : Prop)
    (h105646 : p4789)
    (h84946 : (¬ p5580) ∨ (¬ p3680) ∨ (¬ p5123) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3105) ∨ (¬ p4789) ∨ (¬ p3698) ∨ p2331)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p5580) ∨ (¬ p3680) ∨ (¬ p3105) ∨ p2668 ∨ (¬ p2230) ∨ p2331 ∨ (¬ p3362) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4789 := h105646;
    let u10 : (¬ p3698) := (Or.elim h84946 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115139 (p2230 p2331 p2363 p2668 p2850 p2870 p3246 p3362 p3698 p3950 p4789 : Prop)
    (h105646 : p4789)
    (h87452 : (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3698) ∨ p2668 ∨ (¬ p4789) ∨ (¬ p3362) ∨ (¬ p2230) ∨ p2363 ∨ (¬ p3950) ∨ p2331)
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p2668 ∨ (¬ p3246) ∨ (¬ p3950) ∨ p2331 ∨ p2363 ∨ (¬ p2870) ∨ (¬ p2230) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4789 := h105646;
    let u10 : (¬ p3698) := (Or.elim h87452 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (u4 r8))))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115141 (p2230 p2383 p2668 p2787 p2850 p2870 p3246 p3323 p3362 p3698 p4625 : Prop)
    (h106455 : p4625)
    (h105374 : p2787)
    (h87499 : (¬ p2668) ∨ (¬ p3246) ∨ p3323 ∨ (¬ p2787) ∨ (¬ p2230) ∨ (¬ p4625) ∨ p2383 ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p2870))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3246) ∨ p2383 ∨ (¬ p2668) ∨ (¬ p2870) ∨ p3323 ∨ (¬ p2230) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    let u9 : p2787 := h105374;
    let u10 : (¬ p3698) := (Or.elim h87499 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115145 (p2230 p2241 p2750 p2753 p2850 p3105 p3362 p3449 p3680 p3698 p5123 p5693 : Prop)
    (h106345 : p2750)
    (h94212 : (¬ p5693) ∨ (¬ p2753) ∨ (¬ p2750) ∨ p3449 ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p3105) ∨ (¬ p2241) ∨ (¬ p3698) ∨ (¬ p3362) ∨ (¬ p2230))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ (¬ p3680) ∨ p3449 ∨ (¬ p2230) ∨ (¬ p5123) ∨ (¬ p3105) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p5693) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : (¬ p3698) := (Or.elim h94212 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u3))))))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115153 (p2396 p2417 p2553 p3921 : Prop)
    (h19437 : p2396 ∨ (¬ p2417) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2417) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3921) := (Or.elim h19437 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h101858 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115154 (p2177 p2553 p2911 p3921 : Prop)
    (h82414 : (¬ p2911) ∨ (¬ p3921) ∨ p2177)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2911) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3921) := (Or.elim h82414 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h101858 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115155 (p2553 p2927 p3921 p4427 : Prop)
    (h29221 : (¬ p2927) ∨ (¬ p3921) ∨ p4427)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p4427 ∨ (¬ p2927) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3921) := (Or.elim h29221 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h101858 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115157 (p2298 p2437 p2553 p3921 : Prop)
    (h114307 : p2437 ∨ (¬ p3921) ∨ p2298)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2437 ∨ p2298 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2298) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3921) := (Or.elim h114307 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h101858 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115159 (p2505 p2553 p2922 p3309 p3921 : Prop)
    (h85233 : (¬ p3921) ∨ (¬ p3309) ∨ p2922 ∨ (¬ p2505))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2505) ∨ (¬ p3309) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3921) := (Or.elim h85233 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115160 (p2295 p2437 p2553 p3019 p3921 : Prop)
    (h87223 : (¬ p3019) ∨ (¬ p2295) ∨ p2437 ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3019) ∨ (¬ p2295) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3921) := (Or.elim h87223 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h101858 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115162 (p2177 p2459 p2553 p2573 p3389 p3921 : Prop)
    (h74497 : p2459 ∨ p2177 ∨ p3389 ∨ (¬ p3921) ∨ (¬ p2573))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2459 ∨ p3389 ∨ (¬ p2573) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h74497 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115163 (p2177 p2437 p2459 p2553 p3016 p3921 : Prop)
    (h74506 : p2459 ∨ p2177 ∨ (¬ p3016) ∨ (¬ p3921) ∨ p2437)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2459 ∨ p2177 ∨ (¬ p3016) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h74506 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115164 (p2230 p2274 p2437 p2440 p2553 p3921 : Prop)
    (h74593 : (¬ p3921) ∨ (¬ p2274) ∨ p2437 ∨ p2230 ∨ p2440)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2437 ∨ p2230 ∨ p2440 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h74593 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115165 (p2274 p2553 p2573 p3389 p3921 p3958 : Prop)
    (h105378 : p3958)
    (h74828 : p3389 ∨ (¬ p2274) ∨ (¬ p3921) ∨ (¬ p3958) ∨ (¬ p2573))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ p3389 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p3921) := (Or.elim h74828 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115168 (p2307 p2437 p2553 p2586 p3016 p3921 : Prop)
    (h105372 : p2586)
    (h75161 : (¬ p2307) ∨ (¬ p3921) ∨ p2437 ∨ (¬ p2586) ∨ (¬ p3016))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3016) ∨ (¬ p2307) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2586 := h105372;
    let u5 : (¬ p3921) := (Or.elim h75161 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115169 (p2396 p2553 p2573 p3201 p3422 p3921 : Prop)
    (h77564 : p3201 ∨ p2573 ∨ p2396 ∨ (¬ p3422) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p3201 ∨ p2573 ∨ (¬ p3422) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h77564 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115170 (p2177 p2553 p2573 p3201 p3422 p3921 : Prop)
    (h77574 : p3201 ∨ p2573 ∨ p2177 ∨ (¬ p3921) ∨ (¬ p3422))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2573 ∨ p2177 ∨ (¬ p3422) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h77574 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115171 (p2352 p2553 p3201 p3422 p3921 p4405 : Prop)
    (h105512 : p4405)
    (h77600 : p3201 ∨ (¬ p3422) ∨ (¬ p4405) ∨ (¬ p3921) ∨ (¬ p2352))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2352) ∨ (¬ p3422) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p3921) := (Or.elim h77600 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115172 (p2177 p2553 p3016 p3201 p3422 p3921 : Prop)
    (h77625 : p3201 ∨ p3016 ∨ (¬ p3921) ∨ p2177 ∨ (¬ p3422))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p3201 ∨ p3016 ∨ (¬ p3422) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h77625 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115174 (p2274 p2553 p3201 p3422 p3921 p3958 : Prop)
    (h105378 : p3958)
    (h77718 : p3201 ∨ (¬ p2274) ∨ (¬ p3958) ∨ (¬ p3422) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p3201 ∨ (¬ p3422) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p3921) := (Or.elim h77718 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115177 (p2295 p2553 p2573 p3389 p3921 p4976 : Prop)
    (h105465 : p4976)
    (h79281 : (¬ p2295) ∨ (¬ p3921) ∨ p3389 ∨ (¬ p4976) ∨ (¬ p2573))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ (¬ p2295) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    let u5 : (¬ p3921) := (Or.elim h79281 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115178 (p2177 p2553 p2573 p3016 p3389 p3921 : Prop)
    (h83938 : p3389 ∨ p3016 ∨ (¬ p2573) ∨ (¬ p3921) ∨ p2177)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ p3389 ∨ p3016 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h83938 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115179 (p2493 p2553 p2922 p3564 p3921 p4624 : Prop)
    (h105408 : p4624)
    (h85762 : (¬ p3564) ∨ p2922 ∨ (¬ p4624) ∨ (¬ p2493) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3564) ∨ p2922 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p3921) := (Or.elim h85762 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115180 (p2307 p2493 p2553 p2586 p2922 p3921 : Prop)
    (h105372 : p2586)
    (h85807 : p2922 ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p2493) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2493) ∨ (¬ p2307) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2586 := h105372;
    let u5 : (¬ p3921) := (Or.elim h85807 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115181 (p2230 p2274 p2406 p2553 p3389 p3921 : Prop)
    (h87481 : p2406 ∨ (¬ p2274) ∨ p3389 ∨ (¬ p2230) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p3389 ∨ p2406 ∨ (¬ p2274) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h87481 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115182 (p2437 p2553 p3016 p3564 p3921 p4624 : Prop)
    (h105408 : p4624)
    (h88058 : p2437 ∨ (¬ p3564) ∨ (¬ p4624) ∨ (¬ p3921) ∨ (¬ p3016))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3564) ∨ p2437 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p3921) := (Or.elim h88058 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115183 (p2352 p2553 p2573 p3389 p3921 p4405 : Prop)
    (h105512 : p4405)
    (h88061 : p3389 ∨ (¬ p2573) ∨ (¬ p2352) ∨ (¬ p4405) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ (¬ p2352) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p3921) := (Or.elim h88061 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115184 (p2553 p2573 p3389 p3564 p3921 p4624 : Prop)
    (h105408 : p4624)
    (h88062 : (¬ p3564) ∨ p3389 ∨ (¬ p4624) ∨ (¬ p2573) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3564) ∨ (¬ p2573) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p3921) := (Or.elim h88062 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115185 (p2122 p2553 p2573 p3389 p3921 p5225 : Prop)
    (h105495 : p5225)
    (h88066 : (¬ p2122) ∨ (¬ p3921) ∨ (¬ p2573) ∨ p3389 ∨ (¬ p5225))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ p3389 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    let u5 : (¬ p3921) := (Or.elim h88066 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115186 (p2177 p2493 p2553 p2573 p3389 p3921 : Prop)
    (h99999 : p3389 ∨ (¬ p3921) ∨ p2493 ∨ (¬ p2573) ∨ p2177)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2573) ∨ p2177 ∨ p2493 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h99999 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115187 (p2437 p2553 p2761 p3276 p3343 p3921 : Prop)
    (h100259 : p2761 ∨ (¬ p3276) ∨ p2437 ∨ (¬ p3343) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2761 ∨ (¬ p3276) ∨ p2437 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h100259 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115190 (p2274 p2331 p2437 p2553 p2807 p3921 : Prop)
    (h114329 : p2437 ∨ (¬ p3921) ∨ p2807 ∨ (¬ p2331) ∨ (¬ p2274))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2437 ∨ p2807 ∨ (¬ p2331) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3921) := (Or.elim h114329 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115197 (p2553 p2881 p2911 p3125 p3921 p4204 p4624 : Prop)
    (h105408 : p4624)
    (h82411 : (¬ p2911) ∨ (¬ p3125) ∨ (¬ p4624) ∨ (¬ p4204) ∨ (¬ p3921) ∨ p2881)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2911) ∨ (¬ p3125) ∨ p2881 ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4624 := h105408;
    let u6 : (¬ p3921) := (Or.elim h82411 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115199 (p2230 p2441 p2553 p3093 p3309 p3921 p5193 : Prop)
    (h105488 : p5193)
    (h85236 : (¬ p3921) ∨ (¬ p2441) ∨ (¬ p3309) ∨ p2230 ∨ (¬ p5193) ∨ (¬ p3093))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3309) ∨ (¬ p2441) ∨ p2230 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5193 := h105488;
    let u6 : (¬ p3921) := (Or.elim h85236 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115200 (p2553 p2662 p3016 p3309 p3389 p3921 p3923 : Prop)
    (h85262 : (¬ p3309) ∨ (¬ p3921) ∨ (¬ p2662) ∨ p3389 ∨ (¬ p3016) ∨ (¬ p3923))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p3923) ∨ (¬ p3309) ∨ (¬ p3016) ∨ (¬ p2662) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3921) := (Or.elim h85262 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115201 (p2177 p2493 p2553 p2573 p2922 p3921 p4108 : Prop)
    (h85716 : p2922 ∨ (¬ p4108) ∨ p2177 ∨ (¬ p2493) ∨ p2573 ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2493) ∨ p2573 ∨ (¬ p4108) ∨ p2177 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3921) := (Or.elim h85716 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => r4))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115202 (p2187 p2493 p2553 p2922 p3921 p4203 p4405 : Prop)
    (h105512 : p4405)
    (h85793 : (¬ p3921) ∨ (¬ p2493) ∨ (¬ p4405) ∨ p2922 ∨ (¬ p4203) ∨ (¬ p2187))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2187) ∨ p2922 ∨ (¬ p4203) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p3921) := (Or.elim h85793 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115209 (p2383 p2437 p2553 p2578 p3016 p3921 p4405 : Prop)
    (h105512 : p4405)
    (h98485 : (¬ p2578) ∨ (¬ p2383) ∨ (¬ p4405) ∨ (¬ p3921) ∨ (¬ p3016) ∨ p2437)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2578) ∨ (¬ p2383) ∨ (¬ p3016) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p3921) := (Or.elim h98485 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115217 (p2311 p2341 p2553 p2667 p2911 p3323 p3921 p4624 : Prop)
    (h105408 : p4624)
    (h91760 : (¬ p2911) ∨ (¬ p2667) ∨ (¬ p3323) ∨ (¬ p3921) ∨ p2341 ∨ (¬ p2311) ∨ (¬ p4624))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p2667) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4624 := h105408;
    let u7 : (¬ p3921) := (Or.elim h91760 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115219 (p2383 p2417 p2449 p2553 p3567 p3921 p4067 p4405 : Prop)
    (h105512 : p4405)
    (h100173 : (¬ p2417) ∨ p2449 ∨ (¬ p3921) ∨ (¬ p2383) ∨ (¬ p3567) ∨ (¬ p4067) ∨ (¬ p4405))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p2417) ∨ (¬ p4067) ∨ p2449 ∨ (¬ p3567) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p3921) := (Or.elim h100173 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115220 (p2274 p2341 p2553 p3527 p3575 p3921 p4105 p4514 : Prop)
    (h102002 : (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4105) ∨ p3527 ∨ (¬ p4514) ∨ (¬ p2274) ∨ (¬ p3921))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p4105) ∨ p3527 ∨ (¬ p2274) ∨ (¬ p4514) ∨ (¬ p3575) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3921) := (Or.elim h102002 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => r5))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115226 (p2132 p2307 p2553 p2781 p2911 p3105 p3921 p3941 p4322 p5119 : Prop)
    (h84479 : (¬ p4322) ∨ (¬ p3941) ∨ (¬ p3921) ∨ (¬ p5119) ∨ (¬ p2307) ∨ (¬ p2911) ∨ (¬ p2781) ∨ p2132 ∨ p3105)
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ (¬ p4322) ∨ (¬ p3941) ∨ (¬ p2911) ∨ (¬ p2307) ∨ (¬ p2781) ∨ p3105 ∨ (¬ p5119) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3921) := (Or.elim h84479 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (u6 r7))))))))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115227 (p2307 p2553 p2696 p2781 p2911 p3755 p3921 p3941 p5119 p5284 : Prop)
    (h93301 : (¬ p5284) ∨ (¬ p2911) ∨ p3755 ∨ (¬ p3921) ∨ (¬ p3941) ∨ p2696 ∨ (¬ p2781) ∨ (¬ p5119) ∨ (¬ p2307))
    (h101858 : p3921 ∨ p2553)
    : p2553 ∨ p3755 ∨ (¬ p5284) ∨ (¬ p2911) ∨ (¬ p2307) ∨ p2696 ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3921) := (Or.elim h93301 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h101858 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115238 (p2264 p2807 p3166 p4044 : Prop)
    (h23255 : (¬ p2807) ∨ p3166 ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2807) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4044) := (Or.elim h23255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96457 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115239 (p2264 p2996 p3189 p4044 : Prop)
    (h81953 : p3189 ∨ (¬ p4044) ∨ p2996)
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3189 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4044) := (Or.elim h81953 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96457 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115240 (p2264 p2685 p3005 p4044 : Prop)
    (h87503 : p3005 ∨ (¬ p4044) ∨ (¬ p2685))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2685) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4044) := (Or.elim h87503 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96457 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115241 (p2264 p3580 p4044 p4121 : Prop)
    (h37814 : (¬ p3580) ∨ (¬ p4044) ∨ p4121)
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p4121 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4121) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4044) := (Or.elim h37814 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96457 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115244 (p2246 p2264 p2807 p3189 p4044 : Prop)
    (h23259 : (¬ p2246) ∨ (¬ p2807) ∨ p3189 ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p2246) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4044) := (Or.elim h23259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h96457 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115250 (p2264 p2459 p2911 p3256 p4044 p4653 : Prop)
    (h75183 : p2911 ∨ (¬ p4044) ∨ p2459 ∨ (¬ p4653) ∨ (¬ p3256))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ (¬ p4653) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h75183 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115251 (p2177 p2264 p2459 p3256 p4044 p4361 : Prop)
    (h105382 : p4361)
    (h75186 : p2177 ∨ (¬ p3256) ∨ (¬ p4044) ∨ p2459 ∨ (¬ p4361))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4361 := h105382;
    let u5 : (¬ p4044) := (Or.elim h75186 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115252 (p2241 p2254 p2264 p2996 p3166 p4044 : Prop)
    (h105366 : p2254)
    (h82003 : (¬ p4044) ∨ p3166 ∨ (¬ p2241) ∨ p2996 ∨ (¬ p2254))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2996 ∨ p3166 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2254 := h105366;
    let u5 : (¬ p4044) := (Or.elim h82003 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115253 (p2241 p2264 p2459 p2996 p3256 p4044 : Prop)
    (h82150 : p2996 ∨ (¬ p2241) ∨ p2459 ∨ (¬ p4044) ∨ (¬ p3256))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3256) ∨ p2459 ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h82150 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115254 (p2264 p2459 p2685 p2696 p3256 p4044 : Prop)
    (h89004 : (¬ p3256) ∨ (¬ p4044) ∨ p2459 ∨ (¬ p2696) ∨ (¬ p2685))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h89004 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115255 (p2264 p2459 p2685 p4009 p4044 p5558 : Prop)
    (h45626 : (¬ p2459) ∨ (¬ p2685) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2685) ∨ (¬ p4009) ∨ (¬ p2459) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h45626 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115256 (p2264 p2459 p2807 p4009 p4044 p5558 : Prop)
    (h45512 : (¬ p2459) ∨ (¬ p2807) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4009) ∨ (¬ p5558) ∨ (¬ p2459) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h45512 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115257 (p2177 p2264 p4009 p4044 p4361 p5558 : Prop)
    (h105382 : p4361)
    (h89401 : (¬ p4009) ∨ (¬ p5558) ∨ p2177 ∨ (¬ p4361) ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4009) ∨ (¬ p5558) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4361 := h105382;
    let u5 : (¬ p4044) := (Or.elim h89401 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115258 (p2264 p2449 p3246 p4009 p4044 p5558 : Prop)
    (h100176 : (¬ p4009) ∨ p2449 ∨ (¬ p5558) ∨ (¬ p3246) ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4009) ∨ (¬ p5558) ∨ p2449 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4044) := (Or.elim h100176 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115277 (p2264 p2417 p2651 p3037 p3166 p3631 p4044 : Prop)
    (h95865 : (¬ p3037) ∨ (¬ p2417) ∨ p3166 ∨ (¬ p4044) ∨ p3631 ∨ (¬ p2651))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3166 ∨ (¬ p2417) ∨ (¬ p2651) ∨ p3631 ∨ (¬ p3037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4044) := (Or.elim h95865 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115278 (p2088 p2264 p2717 p3256 p4044 p4403 p4779 : Prop)
    (h97043 : (¬ p4403) ∨ p2088 ∨ (¬ p3256) ∨ (¬ p4044) ∨ p2717 ∨ (¬ p4779))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4403) ∨ (¬ p3256) ∨ (¬ p4779) ∨ p2717 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4044) := (Or.elim h97043 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115279 (p2264 p3146 p3256 p4044 p4075 p4391 p4431 : Prop)
    (h97264 : (¬ p4075) ∨ (¬ p4391) ∨ p3146 ∨ (¬ p4431) ∨ (¬ p3256) ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4391) ∨ (¬ p4075) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4044) := (Or.elim h97264 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115282 (p2264 p2619 p2996 p3256 p3609 p4044 p4392 : Prop)
    (h111993 : p2619 ∨ (¬ p4044) ∨ p3609 ∨ (¬ p3256) ∨ p2996 ∨ (¬ p4392))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2619 ∨ p3609 ∨ (¬ p3256) ∨ p2996 ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4044) := (Or.elim h111993 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115288 (p2088 p2264 p2481 p2509 p3256 p3580 p4044 p4811 : Prop)
    (h105633 : p4811)
    (h92581 : (¬ p3256) ∨ p2088 ∨ (¬ p2509) ∨ (¬ p3580) ∨ (¬ p2481) ∨ (¬ p4044) ∨ (¬ p4811))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2088 ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3580) ∨ (¬ p2481) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4811 := h105633;
    let u7 : (¬ p4044) := (Or.elim h92581 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115300 (p2241 p2264 p2449 p2839 p2870 p2881 p3189 p3449 p4044 : Prop)
    (h112169 : p3189 ∨ p3449 ∨ p2449 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2241) ∨ (¬ p2839) ∨ (¬ p4044))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3189 ∨ p3449 ∨ p2449 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2241) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4044) := (Or.elim h112169 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => r6))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115301 (p2248 p2264 p2352 p2459 p2493 p2807 p3256 p3379 p4044 p4503 : Prop)
    (h105365 : p2248)
    (h106530 : p4503)
    (h75194 : p2493 ∨ p3379 ∨ p2352 ∨ (¬ p3256) ∨ p2459 ∨ (¬ p4044) ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p4503))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2352 ∨ p2459 ∨ p2493 ∨ p3379 ∨ (¬ p2807) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4503 := h106530;
    let u9 : (¬ p4044) := (Or.elim h75194 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115304 (p2177 p2264 p2449 p2696 p3005 p3093 p3309 p4044 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h81826 : p2449 ∨ (¬ p4044) ∨ p2696 ∨ p3005 ∨ (¬ p4736) ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3005 ∨ (¬ p3309) ∨ (¬ p2177) ∨ p2696 ∨ p2449 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4666 := h105658;
    let u9 : (¬ p4044) := (Or.elim h81826 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115305 (p2248 p2264 p2459 p2608 p2807 p2819 p2829 p3256 p4044 p4503 : Prop)
    (h105365 : p2248)
    (h106530 : p4503)
    (h90538 : p2829 ∨ (¬ p2248) ∨ p2819 ∨ p2459 ∨ (¬ p4503) ∨ p2608 ∨ (¬ p4044) ∨ (¬ p2807) ∨ (¬ p3256))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3256) ∨ p2819 ∨ (¬ p2807) ∨ p2459 ∨ p2608 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4503 := h106530;
    let u9 : (¬ p4044) := (Or.elim h90538 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115309 (p2246 p2264 p2459 p2608 p2807 p2819 p2829 p3093 p3256 p4044 : Prop)
    (h113660 : p2829 ∨ p2819 ∨ (¬ p4044) ∨ (¬ p2807) ∨ p3093 ∨ (¬ p3256) ∨ (¬ p2608) ∨ (¬ p2246) ∨ p2459)
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2829 ∨ p2819 ∨ (¬ p2807) ∨ p3093 ∨ (¬ p3256) ∨ (¬ p2608) ∨ (¬ p2246) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4044) := (Or.elim h113660 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115314 (p2187 p2192 p2249 p2264 p2459 p2946 p2996 p3256 p4044 p4282 p4503 : Prop)
    (h106530 : p4503)
    (h106513 : p2249)
    (h82078 : (¬ p4282) ∨ (¬ p2249) ∨ (¬ p4044) ∨ p2946 ∨ p2187 ∨ (¬ p3256) ∨ p2996 ∨ (¬ p4503) ∨ p2192 ∨ p2459)
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2192 ∨ (¬ p3256) ∨ p2187 ∨ p2946 ∨ p2459 ∨ p2996 ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : p2249 := h106513;
    let u10 : (¬ p4044) := (Or.elim h82078 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u5 r8))))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115320 (p2088 p2249 p2264 p2352 p2459 p2493 p2651 p2996 p3171 p3487 p4044 p4503 : Prop)
    (h106530 : p4503)
    (h106513 : p2249)
    (h82134 : p2996 ∨ (¬ p4044) ∨ (¬ p4503) ∨ p2651 ∨ (¬ p2249) ∨ (¬ p2088) ∨ (¬ p3171) ∨ p2459 ∨ p2493 ∨ (¬ p3487) ∨ p2352)
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ p2459 ∨ (¬ p2088) ∨ p2493 ∨ (¬ p3171) ∨ p2352 ∨ p2996 ∨ (¬ p3487) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4503 := h106530;
    let u10 : p2249 := h106513;
    let u11 : (¬ p4044) := (Or.elim h82134 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (u5 r9))))))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115321 (p2264 p2298 p2331 p2797 p2881 p3005 p3399 p3527 p4044 p4236 p4556 p4736 : Prop)
    (h105431 : p4736)
    (h105399 : p4556)
    (h85078 : (¬ p4236) ∨ (¬ p2797) ∨ (¬ p3399) ∨ (¬ p4736) ∨ p3005 ∨ (¬ p4044) ∨ p2881 ∨ (¬ p2298) ∨ p2331 ∨ (¬ p4556) ∨ (¬ p3527))
    (h96457 : p4044 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3527) ∨ p2881 ∨ (¬ p2298) ∨ (¬ p2797) ∨ (¬ p3399) ∨ p2331 ∨ (¬ p4236) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4736 := h105431;
    let u10 : p4556 := h105399;
    let u11 : (¬ p4044) := (Or.elim h85078 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u1))))))))))))))))))))));
    (Or.elim h96457 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115326 (p2284 p2860 p3136 p4316 : Prop)
    (h98949 : p2284 ∨ (¬ p4316) ∨ (¬ p2860))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2284 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4316) := (Or.elim h98949 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h84419 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115327 (p2870 p2901 p3136 p4316 : Prop)
    (h100652 : p2901 ∨ (¬ p4316) ∨ (¬ p2870))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2901 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4316) := (Or.elim h100652 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h84419 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115328 (p2619 p3136 p3156 p4316 : Prop)
    (h100654 : (¬ p2619) ∨ p3156 ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2619) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4316) := (Or.elim h100654 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h84419 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115329 (p2563 p2860 p3136 p3879 p4316 : Prop)
    (h83078 : (¬ p3879) ∨ (¬ p4316) ∨ p2563 ∨ (¬ p2860))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2860) ∨ p2563 ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4316) := (Or.elim h83078 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115330 (p2630 p3136 p3413 p4316 p4392 : Prop)
    (h6729 : (¬ p2630) ∨ (¬ p3413) ∨ (¬ p4316) ∨ (¬ p4392))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p4392) ∨ (¬ p2630) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4316) := (Or.elim h6729 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115332 (p2619 p2901 p3136 p4119 p4316 : Prop)
    (h6607 : (¬ p2619) ∨ p2901 ∨ (¬ p4119) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2619) ∨ p2901 ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4316) := (Or.elim h6607 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h84419 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115333 (p2284 p2396 p2870 p3136 p3246 p4316 : Prop)
    (h78099 : (¬ p3246) ∨ p2396 ∨ (¬ p4316) ∨ p2284 ∨ (¬ p2870))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2284 ∨ (¬ p3246) ∨ (¬ p2870) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h78099 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115341 (p2132 p2696 p2797 p3136 p4316 p4566 : Prop)
    (h106307 : p4566)
    (h92198 : (¬ p4316) ∨ p2132 ∨ (¬ p2797) ∨ (¬ p4566) ∨ (¬ p2696))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2797) ∨ (¬ p2696) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4566 := h106307;
    let u5 : (¬ p4316) := (Or.elim h92198 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115345 (p2737 p2839 p3005 p3136 p4316 p5065 : Prop)
    (h94023 : (¬ p3005) ∨ p2839 ∨ (¬ p5065) ∨ (¬ p2737) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p5065) ∨ (¬ p3005) ∨ (¬ p2737) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p5065 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h94023 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115346 (p2132 p2427 p2696 p2901 p3136 p4316 : Prop)
    (h97971 : p2132 ∨ p2901 ∨ (¬ p2427) ∨ (¬ p4316) ∨ (¬ p2696))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2427) ∨ (¬ p2696) ∨ p2132 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h97971 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115352 (p2132 p2274 p2284 p2696 p3136 p4316 : Prop)
    (h99715 : p2132 ∨ p2274 ∨ p2284 ∨ (¬ p4316) ∨ (¬ p2696))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2274 ∨ p2284 ∨ (¬ p2696) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h99715 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115354 (p2132 p2696 p2751 p2992 p3136 p4316 : Prop)
    (h106343 : p2751)
    (h99747 : p2132 ∨ (¬ p2992) ∨ (¬ p2751) ∨ (¬ p2696) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2992) ∨ (¬ p2696) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p4316) := (Or.elim h99747 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115355 (p2651 p2737 p2811 p2839 p3136 p4316 : Prop)
    (h100381 : (¬ p2737) ∨ p2839 ∨ (¬ p2811) ∨ (¬ p2651) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2839 ∨ (¬ p2651) ∨ (¬ p2811) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h100381 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115356 (p2737 p2839 p2946 p3136 p4316 p4790 : Prop)
    (h106424 : p4790)
    (h100390 : (¬ p2737) ∨ p2839 ∨ (¬ p4790) ∨ (¬ p2946) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2946) ∨ (¬ p2737) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : (¬ p4316) := (Or.elim h100390 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115357 (p2737 p2839 p3115 p3136 p4316 p4322 : Prop)
    (h100394 : (¬ p4322) ∨ (¬ p2737) ∨ (¬ p4316) ∨ p2839 ∨ p3115)
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p3115 ∨ (¬ p4322) ∨ (¬ p2737) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h100394 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115361 (p2098 p2132 p2284 p2619 p3136 p4316 : Prop)
    (h111872 : (¬ p2619) ∨ (¬ p2098) ∨ p2284 ∨ p2132 ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2619) ∨ (¬ p2098) ∨ p2284 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h111872 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115364 (p2807 p2992 p2996 p3136 p4316 p4392 p4790 : Prop)
    (h106424 : p4790)
    (h53105 : (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4316) ∨ (¬ p4392) ∨ (¬ p4790))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p4392) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    let u6 : (¬ p4316) := (Or.elim h53105 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115365 (p2284 p3136 p3246 p3434 p3587 p4316 p4558 : Prop)
    (h105400 : p4558)
    (h89566 : (¬ p4558) ∨ (¬ p3434) ∨ p3246 ∨ p2284 ∨ (¬ p3587) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p3246 ∨ p2284 ∨ (¬ p3587) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p4316) := (Or.elim h89566 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115370 (p2406 p2427 p2870 p3136 p3413 p4316 p4811 : Prop)
    (h105633 : p4811)
    (h97689 : (¬ p2870) ∨ p2427 ∨ (¬ p4811) ∨ (¬ p4316) ∨ p2406 ∨ (¬ p3413))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2427 ∨ p2406 ∨ (¬ p2870) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    let u6 : (¬ p4316) := (Or.elim h97689 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115373 (p2807 p2860 p2946 p3136 p3699 p4316 p4555 : Prop)
    (h105542 : p4555)
    (h99244 : (¬ p2946) ∨ (¬ p3699) ∨ (¬ p4555) ∨ p2807 ∨ (¬ p2860) ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2807 ∨ (¬ p2946) ∨ (¬ p2860) ∨ (¬ p3699) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    let u6 : (¬ p4316) := (Or.elim h99244 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115374 (p2284 p2707 p2839 p3136 p4316 p4344 p4558 : Prop)
    (h105400 : p4558)
    (h99663 : (¬ p2707) ∨ (¬ p4558) ∨ (¬ p4316) ∨ p2839 ∨ p2284 ∨ (¬ p4344))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p2707) ∨ p2284 ∨ p2839 ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p4316) := (Or.elim h99663 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115375 (p2563 p2829 p2839 p3136 p4185 p4316 p4705 : Prop)
    (h106238 : p4705)
    (h99668 : (¬ p2829) ∨ p2839 ∨ (¬ p4185) ∨ (¬ p4316) ∨ (¬ p4705) ∨ p2563)
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p4185) ∨ p2563 ∨ p2839 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p4316) := (Or.elim h99668 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115380 (p2284 p2972 p3105 p3136 p3564 p4316 p5152 : Prop)
    (h110211 : p2972 ∨ (¬ p5152) ∨ (¬ p3105) ∨ p2284 ∨ p3564 ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2972 ∨ (¬ p5152) ∨ (¬ p3105) ∨ p2284 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4316) := (Or.elim h110211 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => r4))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115394 (p2307 p2396 p2608 p2761 p2839 p3136 p4316 p5017 p5405 p5740 : Prop)
    (h75706 : (¬ p2761) ∨ (¬ p5017) ∨ (¬ p2396) ∨ (¬ p5740) ∨ (¬ p5405) ∨ (¬ p4316) ∨ (¬ p2307) ∨ p2608 ∨ p2839)
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p5740) ∨ (¬ p5405) ∨ (¬ p2396) ∨ p2839 ∨ (¬ p2761) ∨ p2608 ∨ (¬ p5017) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4316) := (Or.elim h75706 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115395 (p2122 p2553 p2696 p2753 p2839 p3115 p3136 p3564 p4316 p4368 : Prop)
    (h107633 : (¬ p4316) ∨ p3115 ∨ (¬ p2696) ∨ (¬ p4368) ∨ p2839 ∨ (¬ p2122) ∨ (¬ p3564) ∨ p2553 ∨ (¬ p2753))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ (¬ p4368) ∨ (¬ p3564) ∨ (¬ p2696) ∨ p2839 ∨ (¬ p2122) ∨ p3115 ∨ (¬ p2753) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4316) := (Or.elim h107633 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115415 (p2156 p2192 p2427 p2891 p3741 : Prop)
    (h115035 : (¬ p2427) ∨ p2891 ∨ p2156 ∨ (¬ p2192) ∨ (¬ p3741))
    (h88131 : p3741 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2891 ∨ p2156 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3741) := (Or.elim h115035 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h88131 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115416 (p2274 p4275 p4895 : Prop)
    (h106385 : p4895 ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p4895 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4895) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4275) := (Or.elim h106385 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h90849 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115417 (p2177 p2274 p2881 p4275 : Prop)
    (h78040 : (¬ p2881) ∨ (¬ p4275) ∨ p2177)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2881) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4275) := (Or.elim h78040 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h90849 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115418 (p2274 p2396 p3246 p4275 : Prop)
    (h78075 : (¬ p3246) ∨ p2396 ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3246) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4275) := (Or.elim h78075 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h90849 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115420 (p2274 p2315 p4275 p4986 : Prop)
    (h105368 : p2315)
    (h21893 : (¬ p2315) ∨ (¬ p4275) ∨ p4986)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p4986 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4986) := (fun h => hn (Or.inr h));
    let u2 : p2315 := h105368;
    let u3 : (¬ p4275) := (Or.elim h21893 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h90849 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115421 (p2156 p2274 p2295 p3051 p4275 : Prop)
    (h79312 : p3051 ∨ (¬ p2295) ∨ (¬ p4275) ∨ (¬ p2156))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2156) ∨ (¬ p2295) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4275) := (Or.elim h79312 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115422 (p2274 p2295 p2860 p2870 p4275 : Prop)
    (h86631 : p2870 ∨ (¬ p2295) ∨ (¬ p4275) ∨ (¬ p2860))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2860) ∨ (¬ p2295) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4275) := (Or.elim h86631 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115423 (p2274 p2295 p2427 p2563 p4275 : Prop)
    (h90853 : (¬ p2295) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2427 ∨ (¬ p2563) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4275) := (Or.elim h90853 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h90849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115424 (p2274 p2427 p2553 p3660 p4275 : Prop)
    (h16155 : p2427 ∨ (¬ p2553) ∨ (¬ p3660) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2553) ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4275) := (Or.elim h16155 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h90849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115425 (p2274 p2284 p2295 p2901 p4275 : Prop)
    (h114110 : (¬ p2284) ∨ (¬ p2295) ∨ p2901 ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2284) ∨ (¬ p2295) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4275) := (Or.elim h114110 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h90849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115427 (p2274 p2284 p2553 p2901 p4275 p4718 : Prop)
    (h105425 : p4718)
    (h76974 : p2901 ∨ (¬ p2553) ∨ (¬ p4718) ∨ (¬ p2284) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2901 ∨ (¬ p2284) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    let u5 : (¬ p4275) := (Or.elim h76974 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115430 (p2156 p2177 p2274 p2284 p2901 p4275 : Prop)
    (h78127 : p2901 ∨ (¬ p2284) ∨ p2177 ∨ (¬ p4275) ∨ p2156)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2284) ∨ p2177 ∨ p2901 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h78127 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115431 (p2274 p2284 p2901 p3125 p4275 p4624 : Prop)
    (h105408 : p4624)
    (h78135 : (¬ p3125) ∨ p2901 ∨ (¬ p4275) ∨ (¬ p4624) ∨ (¬ p2284))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3125) ∨ (¬ p2284) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4275) := (Or.elim h78135 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115432 (p2187 p2274 p2284 p2901 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h78174 : p2901 ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4405) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2284) ∨ p2901 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4275) := (Or.elim h78174 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115436 (p2156 p2274 p3051 p3309 p4275 p4518 : Prop)
    (h106113 : p4518)
    (h85162 : p3051 ∨ (¬ p3309) ∨ (¬ p4518) ∨ (¬ p2156) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3309) ∨ (¬ p2156) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4518 := h106113;
    let u5 : (¬ p4275) := (Or.elim h85162 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115437 (p2156 p2274 p2396 p2860 p2870 p4275 : Prop)
    (h85401 : p2870 ∨ p2396 ∨ (¬ p2860) ∨ (¬ p4275) ∨ p2156)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2396 ∨ p2156 ∨ p2870 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h85401 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115441 (p2187 p2274 p2860 p2870 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h86608 : p2870 ∨ (¬ p2187) ∨ (¬ p4405) ∨ (¬ p2860) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2187) ∨ p2870 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4275) := (Or.elim h86608 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115442 (p2177 p2274 p2619 p2870 p4275 p4902 : Prop)
    (h105456 : p4902)
    (h86637 : (¬ p2619) ∨ p2870 ∨ (¬ p4902) ∨ (¬ p4275) ∨ p2177)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2619) ∨ p2870 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4902 := h105456;
    let u5 : (¬ p4275) := (Or.elim h86637 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115443 (p2156 p2177 p2274 p2860 p2870 p4275 : Prop)
    (h86680 : (¬ p2860) ∨ p2870 ∨ p2156 ∨ p2177 ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2156 ∨ p2870 ∨ p2177 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h86680 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115445 (p2122 p2274 p2427 p2563 p2819 p4275 : Prop)
    (h90386 : (¬ p2122) ∨ p2819 ∨ (¬ p2563) ∨ p2427 ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2122) ∨ (¬ p2563) ∨ p2819 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h90386 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115447 (p2177 p2274 p2284 p2427 p2563 p4275 : Prop)
    (h90852 : p2427 ∨ p2284 ∨ (¬ p4275) ∨ (¬ p2563) ∨ p2177)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2284 ∨ p2177 ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h90852 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115448 (p2274 p2307 p2427 p2563 p4275 p4489 : Prop)
    (h105390 : p4489)
    (h90886 : p2427 ∨ (¬ p2307) ∨ (¬ p4275) ∨ (¬ p2563) ∨ (¬ p4489))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2307) ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4489 := h105390;
    let u5 : (¬ p4275) := (Or.elim h90886 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115449 (p2187 p2192 p2274 p2891 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h92647 : p2891 ∨ (¬ p2192) ∨ (¬ p4405) ∨ (¬ p4275) ∨ (¬ p2187))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2192) ∨ (¬ p2187) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4275) := (Or.elim h92647 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115451 (p2192 p2274 p2891 p3125 p4275 p4624 : Prop)
    (h105408 : p4624)
    (h92666 : (¬ p3125) ∨ (¬ p2192) ∨ (¬ p4275) ∨ (¬ p4624) ∨ p2891)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2192) ∨ (¬ p3125) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4275) := (Or.elim h92666 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115452 (p2192 p2274 p2307 p2891 p4275 p4489 : Prop)
    (h105390 : p4489)
    (h92681 : p2891 ∨ (¬ p2307) ∨ (¬ p2192) ∨ (¬ p4489) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2307) ∨ (¬ p2192) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4489 := h105390;
    let u5 : (¬ p4275) := (Or.elim h92681 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115453 (p2156 p2274 p2553 p3051 p4275 p4718 : Prop)
    (h105425 : p4718)
    (h92766 : p3051 ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4718) ∨ (¬ p2156))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2156) ∨ p3051 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    let u5 : (¬ p4275) := (Or.elim h92766 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115454 (p2156 p2274 p2396 p2860 p3051 p4275 : Prop)
    (h92797 : p2860 ∨ (¬ p4275) ∨ (¬ p2156) ∨ p2396 ∨ p3051)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2396 ∨ (¬ p2156) ∨ p2860 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h92797 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115455 (p2156 p2177 p2274 p2563 p3051 p4275 : Prop)
    (h92808 : p3051 ∨ (¬ p4275) ∨ (¬ p2156) ∨ p2563 ∨ p2177)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2156) ∨ p2177 ∨ p3051 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4275) := (Or.elim h92808 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115462 (p2274 p2284 p2383 p2901 p3743 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h78636 : p2901 ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2284) ∨ (¬ p4405) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2284) ∨ (¬ p3743) ∨ p2901 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4275) := (Or.elim h78636 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115463 (p2274 p2427 p2563 p2668 p3745 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h79259 : (¬ p2668) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p4275) ∨ (¬ p4405) ∨ (¬ p3745))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3745) ∨ (¬ p2668) ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4275) := (Or.elim h79259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115467 (p2137 p2156 p2187 p2274 p2870 p4275 p4405 : Prop)
    (h105512 : p4405)
    (h86642 : p2870 ∨ (¬ p2156) ∨ (¬ p4275) ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p4405))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2156) ∨ p2870 ∨ (¬ p2187) ∨ (¬ p2137) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4275) := (Or.elim h86642 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115468 (p2137 p2156 p2274 p2553 p2870 p4275 p4718 : Prop)
    (h105425 : p4718)
    (h86725 : (¬ p2137) ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4718) ∨ p2870 ∨ (¬ p2156))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2137) ∨ (¬ p2553) ∨ (¬ p2156) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4718 := h105425;
    let u6 : (¬ p4275) := (Or.elim h86725 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115469 (p2274 p2311 p2341 p2881 p3654 p4275 p4624 : Prop)
    (h105408 : p4624)
    (h87587 : (¬ p3654) ∨ p2341 ∨ (¬ p2311) ∨ (¬ p2881) ∨ (¬ p4624) ∨ (¬ p4275))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3654) ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4624 := h105408;
    let u6 : (¬ p4275) := (Or.elim h87587 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115472 (p2274 p2449 p3246 p4067 p4228 p4275 p5477 : Prop)
    (h96547 : (¬ p4228) ∨ (¬ p5477) ∨ (¬ p4275) ∨ (¬ p3246) ∨ (¬ p4067) ∨ p2449)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p5477) ∨ (¬ p4228) ∨ (¬ p4067) ∨ (¬ p3246) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4275) := (Or.elim h96547 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115473 (p2192 p2274 p3051 p3125 p3645 p4275 p4624 : Prop)
    (h105408 : p4624)
    (h98996 : (¬ p3125) ∨ p3051 ∨ (¬ p2192) ∨ (¬ p4275) ∨ (¬ p4624) ∨ (¬ p3645))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2192) ∨ (¬ p3125) ∨ p3051 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4624 := h105408;
    let u6 : (¬ p4275) := (Or.elim h98996 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115481 (p2264 p2274 p2881 p3564 p3984 p4067 p4275 p4624 : Prop)
    (h105408 : p4624)
    (h79457 : (¬ p3564) ∨ (¬ p3984) ∨ p2264 ∨ (¬ p4275) ∨ (¬ p4067) ∨ (¬ p2881) ∨ (¬ p4624))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2881) ∨ (¬ p4067) ∨ p2264 ∨ (¬ p3564) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4624 := h105408;
    let u7 : (¬ p4275) := (Or.elim h79457 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115482 (p2274 p3323 p3747 p3969 p4196 p4275 p4624 p5600 : Prop)
    (h105408 : p4624)
    (h50361 : (¬ p3323) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4196) ∨ (¬ p4275) ∨ (¬ p4624) ∨ (¬ p5600))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p5600) ∨ (¬ p3969) ∨ (¬ p3747) ∨ (¬ p4196) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4624 := h105408;
    let u7 : (¬ p4275) := (Or.elim h50361 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115483 (p2122 p2274 p2563 p3051 p3645 p4210 p4275 p4401 : Prop)
    (h91507 : (¬ p4210) ∨ (¬ p2122) ∨ (¬ p3645) ∨ (¬ p4401) ∨ p3051 ∨ (¬ p4275) ∨ (¬ p2563))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p3051 ∨ (¬ p4210) ∨ (¬ p2563) ∨ (¬ p2122) ∨ (¬ p3645) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4275) := (Or.elim h91507 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115485 (p2274 p2668 p3093 p3399 p3922 p4275 p4405 p4909 : Prop)
    (h105512 : p4405)
    (h93368 : p3399 ∨ (¬ p2668) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4909) ∨ (¬ p4405) ∨ (¬ p3093))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p3399 ∨ (¬ p4909) ∨ (¬ p3093) ∨ (¬ p2668) ∨ (¬ p3922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p4275) := (Or.elim h93368 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115489 (p2274 p2449 p2717 p2881 p3941 p4275 p4325 p5612 : Prop)
    (h111799 : p2717 ∨ (¬ p4325) ∨ (¬ p5612) ∨ (¬ p3941) ∨ (¬ p4275) ∨ (¬ p2449) ∨ (¬ p2881))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p2717 ∨ (¬ p4325) ∨ (¬ p5612) ∨ (¬ p3941) ∨ (¬ p2449) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4275) := (Or.elim h111799 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115492 (p2264 p2274 p2685 p2696 p3093 p3246 p3309 p4275 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h85297 : (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4275) ∨ (¬ p3093) ∨ p2685 ∨ p2264 ∨ (¬ p4668) ∨ p2696 ∨ (¬ p4736))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p3309) ∨ p2264 ∨ (¬ p3093) ∨ p2696 ∨ (¬ p3246) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4668 := h105414;
    let u9 : (¬ p4275) := (Or.elim h85297 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115495 (p2274 p2307 p2459 p2630 p2651 p2781 p2881 p3755 p4236 p4275 p5113 : Prop)
    (h105481 : p5113)
    (h86977 : (¬ p2307) ∨ p3755 ∨ (¬ p2459) ∨ (¬ p4275) ∨ (¬ p2881) ∨ (¬ p4236) ∨ (¬ p2781) ∨ (¬ p5113) ∨ (¬ p2630) ∨ p2651)
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ (¬ p2459) ∨ p3755 ∨ (¬ p2781) ∨ (¬ p2630) ∨ (¬ p4236) ∨ (¬ p2881) ∨ p2651 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5113 := h105481;
    let u10 : (¬ p4275) := (Or.elim h86977 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (u7 r8))))))))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115497 (p2274 p2341 p2396 p2881 p3276 p3286 p3670 p3755 p4117 p4275 p5260 : Prop)
    (h112039 : p3755 ∨ p3276 ∨ p2341 ∨ p2396 ∨ (¬ p5260) ∨ (¬ p4117) ∨ (¬ p3670) ∨ (¬ p4275) ∨ (¬ p3286) ∨ (¬ p2881))
    (h90849 : p4275 ∨ p2274)
    : p2274 ∨ p3755 ∨ p3276 ∨ p2341 ∨ p2396 ∨ (¬ p5260) ∨ (¬ p4117) ∨ (¬ p3670) ∨ (¬ p3286) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4275) := (Or.elim h112039 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h90849 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115505 (p3888 p5517 p6134 : Prop)
    (h109370 : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p6134))
    (h9628 : p3888 ∨ (¬ p5517))
    : (¬ p5517) ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5517 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6134 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3888) := (Or.elim h109370 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9628 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115506 (p3888 p5517 p6134 : Prop)
    (h109371 : p6134 ∨ p5517 ∨ (¬ p3888))
    (h14120 : p3888 ∨ p6134)
    : p6134 ∨ p5517 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3888) := (Or.elim h109371 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h14120 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115507 (p5514 p5517 p6134 : Prop)
    (h115505 : (¬ p5517) ∨ (¬ p6134))
    (h108765 : p5517 ∨ p5514)
    : p5514 ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5514) := (fun h => hn (Or.inl h));
    let u1 : p6134 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5517) := (Or.elim h115505 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108765 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115511 (p3888 p5517 p6134 : Prop)
    (h9628 : p3888 ∨ (¬ p5517))
    (h115506 : p6134 ∨ p5517)
    : p6134 ∨ p3888 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3888) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5517) := (Or.elim h9628 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h115506 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step115528 (p2331 p3323 p3564 p3888 p6134 : Prop)
    (h91759 : (¬ p3888) ∨ (¬ p3323) ∨ p3564 ∨ (¬ p2331))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p3323) ∨ (¬ p2331) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3888) := (Or.elim h91759 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115529 (p2573 p3389 p3888 p4435 p6134 : Prop)
    (h94729 : (¬ p3888) ∨ p3389 ∨ (¬ p4435) ∨ (¬ p2573))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4435) ∨ p3389 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3888) := (Or.elim h94729 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115530 (p2437 p3016 p3888 p4329 p6134 : Prop)
    (h94731 : (¬ p3888) ∨ (¬ p4329) ∨ p2437 ∨ (¬ p3016))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4329) ∨ p2437 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3888) := (Or.elim h94731 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115534 (p2331 p2553 p3888 p4228 p6134 : Prop)
    (h110216 : p4228 ∨ (¬ p3888) ∨ p2553 ∨ p2331)
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p4228 ∨ p2553 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3888) := (Or.elim h110216 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115535 (p2440 p3888 p4194 p4228 p6134 : Prop)
    (h110222 : p4228 ∨ (¬ p3888) ∨ p2440 ∨ (¬ p4194))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p4228 ∨ p2440 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3888) := (Or.elim h110222 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115536 (p2363 p2528 p3573 p3888 p5586 p6134 : Prop)
    (h94661 : (¬ p3888) ∨ p2528 ∨ (¬ p3573) ∨ (¬ p5586) ∨ (¬ p2363))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5586) ∨ (¬ p3573) ∨ p2528 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3888) := (Or.elim h94661 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115537 (p2352 p3888 p4771 p5584 p5600 p6134 : Prop)
    (h94694 : (¬ p3888) ∨ (¬ p5600) ∨ (¬ p5584) ∨ p2352 ∨ (¬ p4771))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5584) ∨ (¬ p5600) ∨ p2352 ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3888) := (Or.elim h94694 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115539 (p2284 p2373 p3660 p3888 p4393 p6134 : Prop)
    (h94733 : (¬ p4393) ∨ (¬ p3888) ∨ p2284 ∨ (¬ p3660) ∨ p2373)
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4393) ∨ (¬ p3660) ∨ p2373 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3888) := (Or.elim h94733 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115540 (p2427 p3660 p3888 p4393 p4555 p6134 : Prop)
    (h105542 : p4555)
    (h94734 : (¬ p4393) ∨ (¬ p3888) ∨ (¬ p4555) ∨ p2427 ∨ (¬ p3660))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4393) ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    let u5 : (¬ p3888) := (Or.elim h94734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115542 (p3422 p3641 p3888 p4432 p5586 p6134 : Prop)
    (h94745 : (¬ p3888) ∨ p3641 ∨ (¬ p4432) ∨ (¬ p5586) ∨ (¬ p3422))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5586) ∨ p3641 ∨ (¬ p4432) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3888) := (Or.elim h94745 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115547 (p2440 p3422 p3888 p4153 p4228 p6134 : Prop)
    (h114857 : (¬ p2440) ∨ p4228 ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p3422))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p2440) ∨ p4228 ∨ (¬ p4153) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4228) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3888) := (Or.elim h114857 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115549 (p2230 p3125 p3362 p3660 p3888 p4393 p6134 : Prop)
    (h47932 : (¬ p2230) ∨ (¬ p3125) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4393))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4393) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p2230) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3888) := (Or.elim h47932 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115550 (p2497 p2922 p3660 p3888 p4435 p4646 p6134 : Prop)
    (h105534 : p4646)
    (h58103 : (¬ p2497) ∨ (¬ p2922) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4435) ∨ (¬ p2497) ∨ (¬ p3660) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4646 := h105534;
    let u6 : (¬ p3888) := (Or.elim h58103 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115553 (p2497 p3389 p3519 p3660 p3888 p4435 p4646 p6134 : Prop)
    (h105534 : p4646)
    (h60626 : (¬ p2497) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p4435) ∨ (¬ p3660) ∨ (¬ p2497) ∨ (¬ p3519) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4646 := h105534;
    let u7 : (¬ p3888) := (Or.elim h60626 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115556 (p2132 p2307 p2553 p2781 p3105 p3888 p4322 p5250 p6134 : Prop)
    (h84604 : (¬ p3888) ∨ (¬ p4322) ∨ (¬ p5250) ∨ p2132 ∨ (¬ p2781) ∨ p2553 ∨ p3105 ∨ (¬ p2307))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5250) ∨ p2132 ∨ (¬ p4322) ∨ p3105 ∨ (¬ p2307) ∨ p2553 ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3888) := (Or.elim h84604 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115558 (p2248 p2608 p2651 p3016 p3599 p3670 p3888 p5250 p6134 : Prop)
    (h105365 : p2248)
    (h94287 : (¬ p3888) ∨ p3670 ∨ (¬ p3016) ∨ (¬ p5250) ∨ (¬ p2248) ∨ p3599 ∨ p2608 ∨ (¬ p2651))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5250) ∨ (¬ p3016) ∨ p3599 ∨ p3670 ∨ (¬ p2651) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : (¬ p3888) := (Or.elim h94287 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115559 (p2449 p2598 p2761 p2807 p3422 p3888 p4789 p5250 p6134 : Prop)
    (h105646 : p4789)
    (h94726 : p2761 ∨ (¬ p3888) ∨ p2807 ∨ (¬ p4789) ∨ p2449 ∨ (¬ p5250) ∨ (¬ p2598) ∨ (¬ p3422))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p2761 ∨ p2807 ∨ (¬ p5250) ∨ (¬ p3422) ∨ p2449 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    let u8 : (¬ p3888) := (Or.elim h94726 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115566 (p2246 p2608 p2651 p2744 p3016 p3707 p3830 p3888 p5250 p6134 : Prop)
    (h106503 : p2744)
    (h94727 : (¬ p3888) ∨ p3707 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p2246) ∨ p3830 ∨ (¬ p2651) ∨ (¬ p5250))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p3707 ∨ (¬ p3016) ∨ p3830 ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : (¬ p3888) := (Or.elim h94727 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115568 (p2246 p2651 p2744 p2761 p3016 p3366 p3425 p3434 p3888 p5250 p6134 : Prop)
    (h106503 : p2744)
    (h94724 : (¬ p3888) ∨ p2761 ∨ (¬ p2744) ∨ (¬ p3366) ∨ p3434 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3425) ∨ (¬ p2246) ∨ (¬ p5250))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p3434 ∨ (¬ p3425) ∨ p2761 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : (¬ p3888) := (Or.elim h94724 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115569 (p2252 p2449 p2504 p2608 p2750 p2761 p2807 p3093 p3888 p5250 p6134 : Prop)
    (h106345 : p2750)
    (h94737 : (¬ p3888) ∨ p2761 ∨ (¬ p3093) ∨ p2807 ∨ p2608 ∨ (¬ p2750) ∨ p2449 ∨ (¬ p2504) ∨ (¬ p5250) ∨ (¬ p2252))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p2761 ∨ p2449 ∨ (¬ p3093) ∨ (¬ p5250) ∨ p2807 ∨ (¬ p2252) ∨ (¬ p2504) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    let u10 : (¬ p3888) := (Or.elim h94737 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u6))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115572 (p2307 p2553 p2696 p3366 p3755 p3888 p4866 p5016 p5250 p5284 p6134 : Prop)
    (h106063 : p4866)
    (h94741 : (¬ p5284) ∨ (¬ p3888) ∨ (¬ p3366) ∨ p2696 ∨ (¬ p5250) ∨ p2553 ∨ (¬ p5016) ∨ p3755 ∨ (¬ p2307) ∨ (¬ p4866))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p5284) ∨ p2696 ∨ (¬ p5250) ∨ (¬ p3366) ∨ p3755 ∨ (¬ p5016) ∨ (¬ p2307) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4866 := h106063;
    let u10 : (¬ p3888) := (Or.elim h94741 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115578 (p2246 p2341 p2459 p2651 p2744 p3016 p3266 p3366 p3820 p3888 p5250 p6134 : Prop)
    (h106503 : p2744)
    (h79606 : (¬ p3888) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3366) ∨ p2459 ∨ (¬ p2744) ∨ (¬ p3820) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p2341)
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ (¬ p2246) ∨ p2341 ∨ (¬ p3016) ∨ (¬ p2651) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3366) ∨ (¬ p3820) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : (¬ p3888) := (Or.elim h79606 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (u2 r9))))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step115579 (p2220 p2246 p2651 p2749 p3016 p3146 p3266 p3645 p3888 p4877 p5250 p6134 : Prop)
    (h105451 : p4877)
    (h85651 : (¬ p2246) ∨ (¬ p3888) ∨ p2220 ∨ (¬ p2651) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3016) ∨ p3146 ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p2749))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p3146 ∨ (¬ p3016) ∨ p3266 ∨ p2220 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3645) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4877 := h105451;
    let u11 : (¬ p3888) := (Or.elim h85651 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u7))))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step115581 (p2651 p2753 p2761 p3016 p3051 p3246 p3645 p3888 p4117 p4877 p5250 p6134 : Prop)
    (h105451 : p4877)
    (h92784 : (¬ p3888) ∨ (¬ p2753) ∨ p3246 ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p3016) ∨ p3051 ∨ p2761 ∨ (¬ p5250))
    (h115511 : p6134 ∨ p3888)
    : p6134 ∨ p2761 ∨ (¬ p3645) ∨ p3051 ∨ p3246 ∨ (¬ p5250) ∨ (¬ p3016) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4877 := h105451;
    let u11 : (¬ p3888) := (Or.elim h92784 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (r9 u5))))))))))))))))))))));
    (Or.elim h115511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step115585 (p2341 p2474 p3961 p5197 : Prop)
    (h19490 : p2474 ∨ (¬ p3961) ∨ (¬ p5197))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ p2474 ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2474) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3961) := (Or.elim h19490 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h91609 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115587 (p2088 p2341 p3516 p3961 p4443 : Prop)
    (h101814 : (¬ p3516) ∨ p2088 ∨ (¬ p4443) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3516) ∨ (¬ p4443) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3961) := (Or.elim h101814 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h91609 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115588 (p2341 p2881 p3960 p3961 p4283 : Prop)
    (h13607 : (¬ p2881) ∨ (¬ p3960) ∨ (¬ p3961) ∨ (¬ p4283))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p4283) ∨ (¬ p3960) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3961) := (Or.elim h13607 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115590 (p2341 p2717 p3959 p3960 p3961 : Prop)
    (h5872 : (¬ p2717) ∨ (¬ p3959) ∨ (¬ p3960) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2717) ∨ (¬ p3959) ∨ (¬ p3960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3961) := (Or.elim h5872 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h91609 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115593 (p2088 p2341 p2459 p2911 p3961 p5199 : Prop)
    (h82404 : (¬ p2911) ∨ (¬ p3961) ∨ p2088 ∨ (¬ p2459) ∨ (¬ p5199))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2459) ∨ (¬ p2911) ∨ p2088 ∨ (¬ p5199) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5199 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3961) := (Or.elim h82404 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115598 (p2284 p2341 p3156 p3961 p3969 p5590 : Prop)
    (h90020 : (¬ p3969) ∨ (¬ p5590) ∨ p2284 ∨ (¬ p3156) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3969) ∨ p2284 ∨ (¬ p5590) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3961) := (Or.elim h90020 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115606 (p2088 p2341 p2459 p2717 p3425 p3961 : Prop)
    (h108346 : (¬ p3425) ∨ (¬ p2459) ∨ (¬ p2717) ∨ p2088 ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3425) ∨ (¬ p2459) ∨ (¬ p2717) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3961) := (Or.elim h108346 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115608 (p2177 p2264 p2341 p3961 p4009 p5590 : Prop)
    (h112126 : p2264 ∨ (¬ p4009) ∨ (¬ p3961) ∨ (¬ p2177) ∨ (¬ p5590))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ p2264 ∨ (¬ p4009) ∨ (¬ p2177) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3961) := (Or.elim h112126 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115611 (p2088 p2341 p2459 p2707 p3367 p3959 p3961 : Prop)
    (h88393 : p2088 ∨ (¬ p3367) ∨ (¬ p2459) ∨ (¬ p3961) ∨ p2707 ∨ (¬ p3959))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p3367) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h88393 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115613 (p2341 p2427 p2459 p3941 p3961 p4283 p5590 : Prop)
    (h90022 : (¬ p5590) ∨ (¬ p3941) ∨ p2427 ∨ p2459 ∨ (¬ p4283) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p5590) ∨ (¬ p4283) ∨ (¬ p3941) ∨ p2459 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h90022 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115614 (p2177 p2315 p2341 p2881 p3051 p3961 p4238 : Prop)
    (h105368 : p2315)
    (h92891 : (¬ p3961) ∨ p2881 ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p4238) ∨ p3051)
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2177) ∨ p2881 ∨ p3051 ∨ (¬ p4238) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2315 := h105368;
    let u6 : (¬ p3961) := (Or.elim h92891 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115616 (p2088 p2341 p2363 p3961 p4063 p4138 p5564 : Prop)
    (h93135 : (¬ p4063) ∨ (¬ p5564) ∨ (¬ p2363) ∨ p2088 ∨ (¬ p4138) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p5564) ∨ (¬ p4063) ∨ p2088 ∨ (¬ p4138) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h93135 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115621 (p2088 p2341 p2459 p2630 p2685 p3961 p4155 : Prop)
    (h98440 : (¬ p3961) ∨ p2088 ∨ p2685 ∨ (¬ p4155) ∨ (¬ p2630) ∨ (¬ p2459))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p2459) ∨ p2088 ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h98440 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115622 (p2088 p2341 p2459 p2707 p2737 p3959 p3961 : Prop)
    (h98447 : (¬ p2737) ∨ p2088 ∨ (¬ p2459) ∨ (¬ p3961) ∨ p2707 ∨ (¬ p3959))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p2737) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h98447 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115624 (p2311 p2341 p2352 p2581 p3961 p3979 p5590 : Prop)
    (h105371 : p2581)
    (h49009 : (¬ p2311) ∨ (¬ p2352) ∨ (¬ p2581) ∨ (¬ p3961) ∨ (¬ p3979) ∨ (¬ p5590))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3979) ∨ (¬ p5590) ∨ (¬ p2311) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2581 := h105371;
    let u6 : (¬ p3961) := (Or.elim h49009 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115625 (p2088 p2166 p2192 p2341 p3073 p3961 p4283 : Prop)
    (h111212 : (¬ p2166) ∨ (¬ p4283) ∨ (¬ p3073) ∨ p2088 ∨ p2192 ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2166) ∨ (¬ p4283) ∨ (¬ p3073) ∨ p2088 ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h111212 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => r4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115627 (p2088 p2341 p2881 p3146 p3961 p4063 p5564 : Prop)
    (h114489 : p2881 ∨ (¬ p5564) ∨ (¬ p4063) ∨ p2088 ∨ (¬ p3146) ∨ (¬ p3961))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ p2881 ∨ (¬ p5564) ∨ (¬ p4063) ∨ p2088 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3961) := (Or.elim h114489 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115628 (p2088 p2274 p2318 p2341 p3609 p3961 p4401 p4861 : Prop)
    (h74883 : (¬ p2318) ∨ (¬ p4861) ∨ (¬ p3609) ∨ (¬ p3961) ∨ p2088 ∨ p2274 ∨ (¬ p4401))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p4861) ∨ (¬ p3609) ∨ p2274 ∨ (¬ p4401) ∨ p2088 ∨ (¬ p2318) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3961) := (Or.elim h74883 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115632 (p2088 p2341 p2727 p3073 p3859 p3961 p4155 p4652 : Prop)
    (h105413 : p4652)
    (h80221 : (¬ p3073) ∨ p2088 ∨ (¬ p3961) ∨ (¬ p4155) ∨ (¬ p3859) ∨ (¬ p4652) ∨ p2727)
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3859) ∨ (¬ p3073) ∨ p2088 ∨ (¬ p4155) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4652 := h105413;
    let u7 : (¬ p3961) := (Or.elim h80221 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115633 (p2341 p2406 p2475 p2518 p2901 p3961 p4283 p4702 : Prop)
    (h106079 : p4702)
    (h81484 : (¬ p2518) ∨ p2901 ∨ (¬ p3961) ∨ (¬ p4283) ∨ (¬ p2475) ∨ (¬ p4702) ∨ p2406)
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2475) ∨ p2901 ∨ (¬ p2518) ∨ (¬ p4283) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4702 := h106079;
    let u7 : (¬ p3961) := (Or.elim h81484 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115646 (p2088 p2341 p2685 p2751 p3073 p3859 p3961 p4155 : Prop)
    (h106343 : p2751)
    (h101805 : (¬ p3859) ∨ p2088 ∨ (¬ p3073) ∨ (¬ p3961) ∨ p2685 ∨ (¬ p2751) ∨ (¬ p4155))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p3859) ∨ p2685 ∨ p2088 ∨ (¬ p4155) ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2751 := h106343;
    let u7 : (¬ p3961) := (Or.elim h101805 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115667 (p2088 p2187 p2192 p2255 p2341 p2459 p2946 p2996 p3412 p3961 p4133 p4155 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h85691 : (¬ p4155) ∨ (¬ p2187) ∨ (¬ p3412) ∨ (¬ p2192) ∨ (¬ p2996) ∨ (¬ p3961) ∨ p2088 ∨ (¬ p2946) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2255))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2192) ∨ (¬ p2459) ∨ (¬ p3412) ∨ (¬ p2187) ∨ (¬ p2996) ∨ p2088 ∨ (¬ p2946) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    let u10 : p4133 := h105712;
    let u11 : (¬ p3961) := (Or.elim h85691 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115669 (p2088 p2255 p2341 p2352 p2459 p2493 p2651 p2996 p3961 p4116 p4133 p4155 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h98439 : (¬ p2352) ∨ (¬ p4116) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2996) ∨ (¬ p2493) ∨ (¬ p2255) ∨ p2088 ∨ (¬ p2651) ∨ (¬ p3961) ∨ (¬ p4155))
    (h91609 : p3961 ∨ p2341)
    : p2341 ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p2493) ∨ p2088 ∨ (¬ p4116) ∨ (¬ p4155) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    let u10 : p4133 := h105712;
    let u11 : (¬ p3961) := (Or.elim h98439 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (r9 u7))))))))))))))))))))));
    (Or.elim h91609 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115678 (p4393 p5442 p6118 : Prop)
    (h109030 : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p4393))
    (h9392 : p4393 ∨ (¬ p5442))
    : (¬ p5442) ∨ (¬ p6118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6118 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4393) := (Or.elim h109030 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h9392 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115679 (p4393 p5442 p6118 : Prop)
    (h109031 : p6118 ∨ p5442 ∨ (¬ p4393))
    (h13882 : p4393 ∨ p6118)
    : p6118 ∨ p5442 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4393) := (Or.elim h109031 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h13882 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115680 (p5442 p6118 p6119 : Prop)
    (h115679 : p6118 ∨ p5442)
    (h66613 : (¬ p6118) ∨ (¬ p6119))
    : (¬ p6119) ∨ p5442 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6119 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr h));
    let u2 : p6118 := (Or.elim h115679 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66613 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step115681 (p4393 p5442 p6118 : Prop)
    (h13882 : p4393 ∨ p6118)
    (h115678 : (¬ p5442) ∨ (¬ p6118))
    : (¬ p5442) ∨ p4393 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4393) := (fun h => hn (Or.inr h));
    let u2 : p6118 := (Or.elim h13882 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h115678 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step115685 (p2440 p3016 p4203 p5442 p6116 p6118 : Prop)
    (h110806 : (¬ p6116) ∨ p6118 ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016))
    (h115678 : (¬ p5442) ∨ (¬ p6118))
    : (¬ p5442) ∨ (¬ p6116) ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p6118 := (Or.elim h110806 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115678 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u5)))))

theorem step115691 (p3737 p5442 p6119 : Prop)
    (h13889 : p3737 ∨ p6119)
    (h115680 : (¬ p6119) ∨ p5442)
    : p5442 ∨ p3737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3737) := (fun h => hn (Or.inr h));
    let u2 : p6119 := (Or.elim h13889 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h115680 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u0 r0)))))

theorem step115692 (p2797 p3136 p3745 p5442 p5740 p6119 : Prop)
    (h110171 : p5740 ∨ p6119 ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797)
    (h115680 : (¬ p6119) ∨ p5442)
    : p5442 ∨ p5740 ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5740) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p6119 := (Or.elim h110171 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115680 (fun q0 => (False.elim (q0 u5))) (fun r0 => (False.elim (u0 r0)))))

theorem step115693 (p2850 p3096 p3422 p5442 p6116 p6119 : Prop)
    (h110780 : p6116 ∨ p6119 ∨ (¬ p2850) ∨ p3422 ∨ (¬ p3096))
    (h115680 : (¬ p6119) ∨ p5442)
    : p5442 ∨ p6116 ∨ (¬ p2850) ∨ p3422 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6116) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p6119 := (Or.elim h110780 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115680 (fun q0 => (False.elim (q0 u5))) (fun r0 => (False.elim (u0 r0)))))

theorem step115695 (p2122 p2307 p2860 p3717 p3743 p5442 p6119 : Prop)
    (h113353 : p2860 ∨ p6119 ∨ (¬ p3717) ∨ (¬ p2307) ∨ (¬ p3743) ∨ p2122)
    (h115680 : (¬ p6119) ∨ p5442)
    : p5442 ∨ p2860 ∨ (¬ p3717) ∨ (¬ p2307) ∨ (¬ p3743) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p6119 := (Or.elim h113353 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h115680 (fun q0 => (False.elim (q0 u6))) (fun r0 => (False.elim (u0 r0)))))

theorem step115700 (p2774 p3125 p3737 p4329 p5442 : Prop)
    (h96739 : (¬ p3737) ∨ p2774 ∨ (¬ p4329) ∨ p3125)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p4329) ∨ p3125 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h96739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115701 (p2122 p2156 p3737 p4329 p5442 : Prop)
    (h53321 : (¬ p2122) ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4329))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p4329) ∨ (¬ p2156) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h53321 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115702 (p2241 p2284 p2992 p3737 p5442 : Prop)
    (h44316 : (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p3737))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h44316 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115703 (p2187 p2573 p3737 p5442 p5514 : Prop)
    (h102499 : (¬ p3737) ∨ (¬ p5514) ∨ p2573 ∨ p2187)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5514) ∨ p2573 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h102499 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115704 (p2187 p3422 p3737 p5442 p5514 : Prop)
    (h102503 : (¬ p3737) ∨ (¬ p5514) ∨ p3422 ∨ p2187)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p3422 ∨ (¬ p5514) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h102503 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115705 (p2274 p3737 p5442 p5474 p5503 : Prop)
    (h109054 : (¬ p5474) ∨ (¬ p3737) ∨ (¬ p5503) ∨ p2274)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5474) ∨ (¬ p5503) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h109054 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115707 (p2860 p2870 p3737 p4228 p5442 : Prop)
    (h110215 : p4228 ∨ (¬ p3737) ∨ p2870 ∨ (¬ p2860))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p4228 ∨ p2870 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3737) := (Or.elim h110215 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115708 (p2284 p3156 p3737 p4506 p5442 p5586 : Prop)
    (h79092 : (¬ p5586) ∨ p3156 ∨ (¬ p4506) ∨ (¬ p3737) ∨ (¬ p2284))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5586) ∨ (¬ p2284) ∨ p3156 ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3737) := (Or.elim h79092 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115709 (p2187 p3737 p4503 p5442 p5558 p5584 : Prop)
    (h106530 : p4503)
    (h94692 : (¬ p3737) ∨ (¬ p5558) ∨ (¬ p4503) ∨ p2187 ∨ (¬ p5584))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5584) ∨ (¬ p5558) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    let u5 : (¬ p3737) := (Or.elim h94692 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115710 (p2166 p2192 p3737 p4506 p5442 p5586 : Prop)
    (h96514 : (¬ p3737) ∨ (¬ p5586) ∨ (¬ p4506) ∨ p2166 ∨ (¬ p2192))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5586) ∨ (¬ p4506) ∨ (¬ p2192) ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3737) := (Or.elim h96514 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115714 (p2427 p2590 p3737 p4558 p5442 p5514 : Prop)
    (h105400 : p4558)
    (h51513 : (¬ p2427) ∨ (¬ p2590) ∨ (¬ p3737) ∨ (¬ p4558) ∨ (¬ p5514))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5514) ∨ (¬ p2590) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    let u5 : (¬ p3737) := (Or.elim h51513 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115715 (p2156 p3125 p3461 p3737 p4032 p5442 : Prop)
    (h112438 : p3125 ∨ (¬ p3461) ∨ (¬ p3737) ∨ (¬ p4032) ∨ (¬ p2156))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p3125 ∨ (¬ p3461) ∨ (¬ p4032) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3737) := (Or.elim h112438 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115716 (p2156 p2373 p3737 p4109 p4506 p5442 p5586 : Prop)
    (h96513 : (¬ p3737) ∨ (¬ p5586) ∨ p2373 ∨ (¬ p4506) ∨ (¬ p2156) ∨ (¬ p4109))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5586) ∨ (¬ p4109) ∨ (¬ p4506) ∨ (¬ p2156) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3737) := (Or.elim h96513 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115721 (p2274 p2957 p3136 p3370 p3737 p4435 p4512 p5442 : Prop)
    (h96711 : (¬ p3370) ∨ (¬ p4435) ∨ p3136 ∨ (¬ p2957) ∨ (¬ p3737) ∨ (¬ p4512) ∨ p2274)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p4435) ∨ p2274 ∨ (¬ p2957) ∨ (¬ p3370) ∨ (¬ p4512) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3737) := (Or.elim h96711 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115722 (p2284 p2427 p2504 p2590 p3413 p3737 p4435 p5442 : Prop)
    (h46923 : (¬ p2284) ∨ (¬ p2427) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3413) ∨ (¬ p3737) ∨ (¬ p4435))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p4435) ∨ (¬ p3413) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p2284) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3737) := (Or.elim h46923 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115724 (p2132 p2417 p2761 p2860 p3389 p3737 p4729 p5250 p5442 : Prop)
    (h105429 : p4729)
    (h81913 : p2417 ∨ p2761 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4729) ∨ (¬ p5250) ∨ (¬ p3737) ∨ p3389)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p2761 ∨ (¬ p2132) ∨ p2417 ∨ (¬ p2860) ∨ p3389 ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    let u8 : (¬ p3737) := (Or.elim h81913 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115730 (p2132 p2449 p2761 p2807 p2860 p3737 p4789 p5250 p5442 : Prop)
    (h105646 : p4789)
    (h100170 : (¬ p3737) ∨ p2807 ∨ (¬ p2132) ∨ (¬ p2860) ∨ p2761 ∨ (¬ p5250) ∨ p2449 ∨ (¬ p4789))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p2761 ∨ p2449 ∨ (¬ p5250) ∨ p2807 ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    let u8 : (¬ p3737) := (Or.elim h100170 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115731 (p2132 p2761 p2860 p3399 p3631 p3737 p4733 p5250 p5442 : Prop)
    (h105430 : p4733)
    (h101985 : (¬ p3737) ∨ p2761 ∨ (¬ p2860) ∨ p3399 ∨ (¬ p4733) ∨ (¬ p5250) ∨ (¬ p2132) ∨ p3631)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p2761 ∨ p3399 ∨ (¬ p2132) ∨ (¬ p2860) ∨ p3631 ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : (¬ p3737) := (Or.elim h101985 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115733 (p2192 p2210 p2761 p3425 p3434 p3737 p4736 p5250 p5442 : Prop)
    (h105431 : p4736)
    (h102166 : (¬ p3737) ∨ (¬ p5250) ∨ (¬ p2192) ∨ (¬ p4736) ∨ p3434 ∨ (¬ p3425) ∨ (¬ p2210) ∨ p2761)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p2192) ∨ p2761 ∨ (¬ p3425) ∨ p3434 ∨ (¬ p2210) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : (¬ p3737) := (Or.elim h102166 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u2 r6))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115735 (p2187 p2563 p3156 p3737 p3955 p4153 p4328 p4329 p5442 : Prop)
    (h114428 : (¬ p2187) ∨ (¬ p3737) ∨ (¬ p4329) ∨ (¬ p3156) ∨ (¬ p2563) ∨ (¬ p4328) ∨ (¬ p4153) ∨ (¬ p3955))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p2187) ∨ (¬ p4329) ∨ (¬ p3156) ∨ (¬ p2563) ∨ (¬ p4328) ∨ (¬ p4153) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3737) := (Or.elim h114428 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115736 (p2132 p2192 p2737 p3166 p3361 p3737 p4418 p5442 p5582 p5600 : Prop)
    (h88547 : (¬ p3737) ∨ (¬ p5600) ∨ (¬ p2132) ∨ (¬ p5582) ∨ p2737 ∨ (¬ p4418) ∨ (¬ p3361) ∨ p3166 ∨ (¬ p2192))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p5600) ∨ p3166 ∨ p2737 ∨ (¬ p2192) ∨ (¬ p3361) ∨ (¬ p2132) ∨ (¬ p4418) ∨ (¬ p5582) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3737) := (Or.elim h88547 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115741 (p2132 p2341 p2459 p2860 p3266 p3737 p4729 p5197 p5250 p5442 : Prop)
    (h105429 : p4729)
    (h102248 : (¬ p3737) ∨ (¬ p2860) ∨ p2341 ∨ p3266 ∨ (¬ p2132) ∨ (¬ p5250) ∨ (¬ p5197) ∨ p2459 ∨ (¬ p4729))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p3266 ∨ p2341 ∨ p2459 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p5197) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    let u9 : (¬ p3737) := (Or.elim h102248 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115746 (p2761 p3093 p3125 p3425 p3516 p3737 p4066 p4325 p4435 p4733 p5442 : Prop)
    (h105430 : p4733)
    (h99888 : (¬ p3737) ∨ (¬ p4435) ∨ (¬ p4325) ∨ p3125 ∨ (¬ p3516) ∨ p3425 ∨ (¬ p4066) ∨ (¬ p2761) ∨ p3093 ∨ (¬ p4733))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ (¬ p4435) ∨ p3125 ∨ (¬ p3516) ∨ p3425 ∨ (¬ p4066) ∨ (¬ p4325) ∨ p3093 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4733 := h105430;
    let u10 : (¬ p3737) := (Or.elim h99888 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115747 (p2192 p2253 p2761 p2946 p3412 p3425 p3434 p3737 p4736 p5250 p5442 : Prop)
    (h105431 : p4736)
    (h102167 : p2761 ∨ (¬ p3412) ∨ (¬ p4736) ∨ (¬ p2946) ∨ (¬ p5250) ∨ p3434 ∨ (¬ p2253) ∨ (¬ p2192) ∨ (¬ p3425) ∨ (¬ p3737))
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p2761 ∨ (¬ p2192) ∨ (¬ p3425) ∨ p3434 ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4736 := h105431;
    let u10 : (¬ p3737) := (Or.elim h102167 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => r8))))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115750 (p2274 p2331 p2996 p3201 p3276 p3333 p3737 p3922 p4325 p4435 p5442 : Prop)
    (h111426 : p3201 ∨ (¬ p4435) ∨ p4325 ∨ p2996 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3922) ∨ (¬ p3737) ∨ p2274 ∨ p2331)
    (h115691 : p5442 ∨ p3737)
    : p5442 ∨ p3201 ∨ (¬ p4435) ∨ p4325 ∨ p2996 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3922) ∨ p2274 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p4325) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3737) := (Or.elim h111426 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h115691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115755 (p3125 p3461 p4393 p5442 : Prop)
    (h109131 : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p3125))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4393) := (Or.elim h109131 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step115756 (p2563 p2598 p2850 p4393 p5442 : Prop)
    (h96097 : (¬ p4393) ∨ p2850 ∨ p2598 ∨ p2563)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p2850 ∨ p2598 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h96097 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115757 (p2187 p2331 p4228 p4393 p5442 : Prop)
    (h46440 : (¬ p2187) ∨ (¬ p2331) ∨ (¬ p4228) ∨ (¬ p4393))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p4228) ∨ (¬ p2187) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h46440 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115758 (p2284 p2696 p3136 p4393 p5442 : Prop)
    (h96120 : (¬ p4393) ∨ p3136 ∨ p2284 ∨ p2696)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p2284 ∨ p3136 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h96120 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115759 (p2274 p3093 p4393 p4435 p5442 : Prop)
    (h111297 : p4435 ∨ (¬ p4393) ∨ (¬ p3093) ∨ (¬ p2274))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p4435 ∨ (¬ p3093) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4435) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h111297 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115760 (p2860 p4338 p4393 p4435 p5442 : Prop)
    (h111300 : p4435 ∨ (¬ p4393) ∨ p2860 ∨ (¬ p4338))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p4435 ∨ p2860 ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4435) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h111300 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115761 (p2427 p3660 p4393 p5442 p6134 : Prop)
    (h115540 : p6134 ∨ (¬ p4393) ∨ (¬ p3660) ∨ p2427)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p6134 ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6134) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4393) := (Or.elim h115540 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115762 (p2860 p2870 p4140 p4393 p5442 p5472 : Prop)
    (h83357 : (¬ p4393) ∨ (¬ p5472) ∨ (¬ p2870) ∨ (¬ p4140) ∨ p2860)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p5472) ∨ (¬ p4140) ∨ (¬ p2870) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4393) := (Or.elim h83357 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115764 (p2156 p3051 p4140 p4393 p5442 p5472 : Prop)
    (h96111 : (¬ p4393) ∨ (¬ p4140) ∨ p2156 ∨ (¬ p3051) ∨ (¬ p5472))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p5472) ∨ (¬ p4140) ∨ p2156 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4393) := (Or.elim h96111 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115765 (p2284 p2901 p4140 p4393 p5442 p5472 : Prop)
    (h96117 : (¬ p4393) ∨ (¬ p4140) ∨ (¬ p5472) ∨ p2284 ∨ (¬ p2901))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p5472) ∨ (¬ p2901) ∨ (¬ p4140) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4393) := (Or.elim h96117 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115767 (p2563 p2797 p3323 p3914 p4393 p5442 : Prop)
    (h113927 : p2797 ∨ (¬ p4393) ∨ p3323 ∨ p2563 ∨ (¬ p3914))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p2797 ∨ p3323 ∨ p2563 ∨ (¬ p3914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4393) := (Or.elim h113927 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115768 (p2284 p2373 p3660 p4393 p5442 p6134 : Prop)
    (h115539 : p6134 ∨ (¬ p4393) ∨ (¬ p3660) ∨ p2373 ∨ p2284)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p6134 ∨ (¬ p3660) ∨ p2373 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6134) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4393) := (Or.elim h115539 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115771 (p2230 p2655 p2850 p3096 p3422 p4393 p5442 : Prop)
    (h87910 : (¬ p4393) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p2655) ∨ p3422 ∨ p2230)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p3422 ∨ (¬ p2850) ∨ p2230 ∨ (¬ p2655) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4393) := (Or.elim h87910 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115774 (p2192 p2284 p3156 p3747 p4228 p4393 p5442 : Prop)
    (h114141 : (¬ p2284) ∨ (¬ p4228) ∨ (¬ p4393) ∨ p2192 ∨ (¬ p3747) ∨ p3156)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p2284) ∨ (¬ p4228) ∨ p2192 ∨ (¬ p3747) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4393) := (Or.elim h114141 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115775 (p2156 p2284 p3156 p3747 p4228 p4393 p5442 : Prop)
    (h114142 : (¬ p2284) ∨ (¬ p4228) ∨ (¬ p4393) ∨ p2156 ∨ (¬ p3747) ∨ p3156)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p2284) ∨ (¬ p4228) ∨ p2156 ∨ (¬ p3747) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4393) := (Or.elim h114142 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115777 (p2230 p3125 p3362 p3660 p4393 p5442 p6134 : Prop)
    (h115549 : p6134 ∨ (¬ p4393) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p2230) ∨ (¬ p3125))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p6134 ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p2230) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6134) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4393) := (Or.elim h115549 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115780 (p2156 p2187 p2957 p3156 p3955 p4393 p5442 p5472 : Prop)
    (h114423 : (¬ p2187) ∨ (¬ p5472) ∨ (¬ p4393) ∨ (¬ p2957) ∨ (¬ p3955) ∨ p2156 ∨ (¬ p3156))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p2187) ∨ (¬ p5472) ∨ (¬ p2957) ∨ (¬ p3955) ∨ p2156 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114423 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115781 (p2284 p2946 p3193 p3276 p3379 p3461 p4393 p5442 : Prop)
    (h114908 : (¬ p3461) ∨ p3193 ∨ (¬ p3276) ∨ (¬ p3379) ∨ p2946 ∨ p2284 ∨ (¬ p4393))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ p3193 ∨ (¬ p3276) ∨ (¬ p3379) ∨ p2946 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114908 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => r5))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115782 (p2132 p2761 p2860 p3399 p3461 p3631 p4393 p5442 : Prop)
    (h114909 : (¬ p3461) ∨ (¬ p3399) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p3631) ∨ (¬ p4393) ∨ p2132)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p3399) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p3631) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114909 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (u6 r5))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115783 (p2192 p2210 p2761 p3425 p3434 p3461 p4393 p5442 : Prop)
    (h114918 : (¬ p3461) ∨ (¬ p3434) ∨ p2210 ∨ p3425 ∨ (¬ p2761) ∨ (¬ p4393) ∨ p2192)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p3434) ∨ p2210 ∨ p3425 ∨ (¬ p2761) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (u6 r5))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115784 (p2132 p2449 p2761 p2807 p2860 p3461 p4393 p5442 : Prop)
    (h114919 : (¬ p3461) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2132 ∨ p2860 ∨ (¬ p4393) ∨ (¬ p2807))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2132 ∨ p2860 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114919 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115785 (p2132 p2860 p3166 p3256 p3266 p3461 p4393 p5442 : Prop)
    (h114920 : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p3256) ∨ p2860 ∨ p2132 ∨ (¬ p3166) ∨ (¬ p3266))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p3256) ∨ p2860 ∨ p2132 ∨ (¬ p3166) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4393) := (Or.elim h114920 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115787 (p2284 p2341 p2459 p2946 p3266 p3461 p4393 p4850 p5442 : Prop)
    (h108416 : p3461 ∨ (¬ p3266) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2284 ∨ p2946)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ p3461 ∨ (¬ p3266) ∨ (¬ p4850) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2284 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4393) := (Or.elim h108416 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115789 (p2284 p2341 p2459 p2946 p3266 p3461 p4393 p4850 p5442 : Prop)
    (h114915 : (¬ p3461) ∨ (¬ p4393) ∨ p2284 ∨ (¬ p2341) ∨ p2946 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4850))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ p2284 ∨ (¬ p2341) ∨ p2946 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4393) := (Or.elim h114915 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115790 (p2132 p2417 p2761 p2860 p3389 p3461 p4393 p4419 p5442 : Prop)
    (h114917 : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p2417) ∨ p2132 ∨ (¬ p4419) ∨ (¬ p3389))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p2417) ∨ p2132 ∨ (¬ p4419) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4393) := (Or.elim h114917 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115795 (p2252 p2284 p2608 p2946 p3461 p3707 p3830 p4393 p5442 : Prop)
    (h114942 : (¬ p3461) ∨ (¬ p4393) ∨ p2284 ∨ (¬ p3830) ∨ (¬ p3707) ∨ (¬ p2252) ∨ p2608 ∨ p2946)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ p2284 ∨ (¬ p3830) ∨ (¬ p3707) ∨ (¬ p2252) ∨ p2608 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4393) := (Or.elim h114942 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115798 (p2249 p2641 p2651 p3125 p3193 p3276 p3487 p4228 p4393 p5442 : Prop)
    (h106513 : p2249)
    (h96107 : (¬ p4228) ∨ (¬ p4393) ∨ p2651 ∨ (¬ p3125) ∨ (¬ p2249) ∨ p3276 ∨ (¬ p3487) ∨ (¬ p2641) ∨ (¬ p3193))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3125) ∨ p3276 ∨ p2651 ∨ (¬ p2641) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p4228) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : (¬ p4393) := (Or.elim h96107 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115810 (p2284 p2761 p2946 p3361 p3425 p3434 p3461 p3619 p4393 p4778 p5442 : Prop)
    (h114972 : (¬ p3461) ∨ (¬ p3434) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p3361) ∨ (¬ p3619) ∨ (¬ p4393) ∨ p2946 ∨ p2284 ∨ (¬ p4778))
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ (¬ p3434) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p3361) ∨ (¬ p3619) ∨ p2946 ∨ p2284 ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4393) := (Or.elim h114972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115813 (p2230 p2241 p2860 p3366 p3461 p3695 p3707 p3830 p3905 p4393 p5442 : Prop)
    (h114980 : (¬ p3461) ∨ (¬ p4393) ∨ p2860 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2230 ∨ p2241)
    (h115681 : (¬ p5442) ∨ p4393)
    : (¬ p5442) ∨ (¬ p3461) ∨ p2860 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2230 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4393) := (Or.elim h114980 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h115681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115817 (p2440 p3083 p3878 p4355 : Prop)
    (h113732 : p3083 ∨ (¬ p3878) ∨ (¬ p4355) ∨ p2440)
    (h93398 : p3878 ∨ p3083)
    : p3083 ∨ (¬ p4355) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3878) := (Or.elim h113732 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h93398 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115818 (p2307 p2383 p3955 p4113 : Prop)
    (h114593 : (¬ p2383) ∨ (¬ p4113) ∨ p2307 ∨ (¬ p3955))
    (h96435 : p4113 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2307 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4113) := (Or.elim h114593 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96435 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115820 (p2383 p2608 p2819 p2829 p4113 p5017 : Prop)
    (h114613 : (¬ p2383) ∨ p2829 ∨ p2608 ∨ p2819 ∨ (¬ p4113) ∨ (¬ p5017))
    (h96435 : p4113 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2829 ∨ p2608 ∨ p2819 ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4113) := (Or.elim h114613 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96435 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115823 (p5659 p5660 p6172 : Prop)
    (h109701 : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172))
    (h10119 : (¬ p5659) ∨ p5660)
    : (¬ p5659) ∨ (¬ p6172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5660) := (Or.elim h109701 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h10119 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u2 r0)))))

theorem step115824 (p5659 p5660 p6172 : Prop)
    (h109703 : p6172 ∨ (¬ p5660) ∨ p5659)
    (h15001 : p5660 ∨ p6172)
    : p6172 ∨ p5659 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5659) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5660) := (Or.elim h109703 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h15001 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115825 (p4129 p5659 p6172 : Prop)
    (h115823 : (¬ p5659) ∨ (¬ p6172))
    (h108573 : p5659 ∨ p4129)
    : p4129 ∨ (¬ p6172) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4129) := (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5659) := (Or.elim h115823 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108573 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step115826 (p5659 p5660 p6172 : Prop)
    (h10119 : (¬ p5659) ∨ p5660)
    (h115824 : p6172 ∨ p5659)
    : p6172 ∨ p5660 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5660) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5659) := (Or.elim h10119 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h115824 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step115828 (p3791 p4140 p5659 p6172 : Prop)
    (h109700 : (¬ p5659) ∨ (¬ p3791) ∨ (¬ p4140))
    (h115824 : p6172 ∨ p5659)
    : p6172 ∨ (¬ p3791) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5659) := (Or.elim h109700 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h115824 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step115829 (p2685 p3136 p4333 p5659 p5740 p6172 : Prop)
    (h108570 : (¬ p5659) ∨ (¬ p5740) ∨ (¬ p4333) ∨ p3136 ∨ (¬ p2685))
    (h115824 : p6172 ∨ p5659)
    : p6172 ∨ (¬ p5740) ∨ (¬ p4333) ∨ p3136 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5659) := (Or.elim h108570 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115824 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115836 (p2417 p2901 p3868 p5660 p6172 : Prop)
    (h97218 : (¬ p3868) ∨ (¬ p5660) ∨ p2417 ∨ p2901)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3868) ∨ p2901 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h97218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115837 (p2427 p3587 p4253 p5660 p6172 : Prop)
    (h107202 : (¬ p5660) ∨ (¬ p4253) ∨ p2427 ∨ (¬ p3587))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4253) ∨ (¬ p3587) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h107202 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115838 (p2881 p3399 p4075 p5660 p6172 : Prop)
    (h47885 : (¬ p2881) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5660))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4075) ∨ (¬ p2881) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h47885 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115840 (p2396 p2891 p3791 p5660 p6172 : Prop)
    (h98786 : (¬ p3791) ∨ (¬ p5660) ∨ p2396 ∨ p2891)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3791) ∨ p2396 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h98786 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115843 (p2807 p2881 p3931 p5660 p6172 : Prop)
    (h47444 : (¬ p2807) ∨ (¬ p2881) ∨ (¬ p3931) ∨ (¬ p5660))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3931) ∨ (¬ p2881) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h47444 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115844 (p2901 p3115 p4075 p5660 p6172 : Prop)
    (h99092 : (¬ p4075) ∨ (¬ p3115) ∨ (¬ p5660) ∨ p2901)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4075) ∨ (¬ p3115) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5660) := (Or.elim h99092 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step115847 (p2427 p4075 p4431 p4632 p5660 p6172 : Prop)
    (h106257 : p4632)
    (h76908 : (¬ p5660) ∨ (¬ p4075) ∨ p2427 ∨ (¬ p4431) ∨ (¬ p4632))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4075) ∨ (¬ p4431) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    let u5 : (¬ p5660) := (Or.elim h76908 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115848 (p2187 p3309 p3791 p4204 p5660 p6172 : Prop)
    (h44635 : (¬ p2187) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4204) ∨ (¬ p5660))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3791) ∨ (¬ p2187) ∨ (¬ p4204) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5660) := (Or.elim h44635 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115849 (p2166 p2891 p4042 p5559 p5660 p6172 : Prop)
    (h106189 : p5559)
    (h92712 : p2891 ∨ (¬ p2166) ∨ (¬ p5660) ∨ (¬ p5559) ∨ (¬ p4042))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p2166) ∨ (¬ p4042) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5559 := h106189;
    let u5 : (¬ p5660) := (Or.elim h92712 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115852 (p2563 p3741 p3868 p4558 p5660 p6172 : Prop)
    (h105400 : p4558)
    (h97225 : (¬ p5660) ∨ (¬ p3868) ∨ (¬ p3741) ∨ p2563 ∨ (¬ p4558))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3868) ∨ (¬ p3741) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    let u5 : (¬ p5660) := (Or.elim h97225 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115853 (p2901 p3587 p4253 p5053 p5660 p6172 : Prop)
    (h97240 : (¬ p4253) ∨ (¬ p5660) ∨ (¬ p3587) ∨ (¬ p5053) ∨ p2901)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4253) ∨ p2901 ∨ (¬ p3587) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5660) := (Or.elim h97240 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115854 (p2373 p2427 p4042 p5559 p5660 p6172 : Prop)
    (h106189 : p5559)
    (h98757 : (¬ p5660) ∨ (¬ p5559) ∨ (¬ p2373) ∨ (¬ p4042) ∨ p2427)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4042) ∨ (¬ p2373) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5559 := h106189;
    let u5 : (¬ p5660) := (Or.elim h98757 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115855 (p2177 p2563 p3791 p4204 p5660 p6172 : Prop)
    (h98796 : (¬ p3791) ∨ (¬ p5660) ∨ (¬ p4204) ∨ p2563 ∨ p2177)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3791) ∨ p2177 ∨ p2563 ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5660) := (Or.elim h98796 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115859 (p2881 p2995 p3156 p3931 p5660 p6172 : Prop)
    (h109426 : p2881 ∨ (¬ p3931) ∨ (¬ p5660) ∨ (¬ p2995) ∨ p3156)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ p2881 ∨ (¬ p3931) ∨ (¬ p2995) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5660) := (Or.elim h109426 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115860 (p2187 p2619 p2870 p3550 p5660 p6172 : Prop)
    (h114411 : (¬ p2187) ∨ (¬ p5660) ∨ (¬ p3550) ∨ p2870 ∨ (¬ p2619))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p2187) ∨ (¬ p3550) ∨ p2870 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5660) := (Or.elim h114411 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step115862 (p2132 p2707 p2839 p3873 p4169 p5660 p6172 : Prop)
    (h83786 : (¬ p5660) ∨ p2132 ∨ p2707 ∨ (¬ p4169) ∨ (¬ p2839) ∨ (¬ p3873))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ p2707 ∨ (¬ p2839) ∨ (¬ p3873) ∨ p2132 ∨ (¬ p4169) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5660) := (Or.elim h83786 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115864 (p2901 p4075 p4338 p4452 p4960 p5660 p6172 : Prop)
    (h106209 : p4960)
    (h91539 : (¬ p5660) ∨ (¬ p4075) ∨ (¬ p4338) ∨ p2901 ∨ (¬ p4960) ∨ (¬ p4452))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4075) ∨ p2901 ∨ (¬ p4338) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4960 := h106209;
    let u6 : (¬ p5660) := (Or.elim h91539 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115872 (p2187 p2406 p2922 p4075 p4204 p5660 p6172 : Prop)
    (h112397 : (¬ p2922) ∨ (¬ p5660) ∨ (¬ p4075) ∨ (¬ p4204) ∨ p2406 ∨ (¬ p2187))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p2922) ∨ (¬ p4075) ∨ (¬ p4204) ∨ p2406 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5660) := (Or.elim h112397 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step115873 (p2132 p2187 p3366 p3687 p4075 p4204 p5660 p6172 : Prop)
    (h83022 : (¬ p5660) ∨ (¬ p3687) ∨ (¬ p4075) ∨ (¬ p3366) ∨ (¬ p2187) ∨ (¬ p4204) ∨ p2132)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p4075) ∨ (¬ p4204) ∨ (¬ p3366) ∨ (¬ p2187) ∨ p2132 ∨ (¬ p3687) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5660) := (Or.elim h83022 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step115877 (p2254 p2901 p2946 p3193 p3276 p3379 p4831 p5660 p6172 : Prop)
    (h105366 : p2254)
    (h105445 : p4831)
    (h78144 : p3193 ∨ (¬ p4831) ∨ p2946 ∨ p2901 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p3276) ∨ (¬ p5660))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3276) ∨ p2946 ∨ p2901 ∨ p3193 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4831 := h105445;
    let u8 : (¬ p5660) := (Or.elim h78144 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => r6))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115878 (p2230 p2427 p3073 p3266 p3449 p4831 p5193 p5660 p6172 : Prop)
    (h105488 : p5193)
    (h105445 : p4831)
    (h80215 : (¬ p5660) ∨ (¬ p3266) ∨ (¬ p3073) ∨ (¬ p4831) ∨ p2427 ∨ (¬ p5193) ∨ p2230 ∨ (¬ p3449))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3449) ∨ (¬ p3266) ∨ p2230 ∨ p2427 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4831 := h105445;
    let u8 : (¬ p5660) := (Or.elim h80215 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115881 (p2230 p2241 p2427 p3506 p3842 p4831 p5193 p5660 p6172 : Prop)
    (h105488 : p5193)
    (h105445 : p4831)
    (h94402 : (¬ p5660) ∨ (¬ p3506) ∨ p2230 ∨ (¬ p4831) ∨ p2427 ∨ (¬ p3842) ∨ (¬ p2241) ∨ (¬ p5193))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3842) ∨ p2427 ∨ (¬ p3506) ∨ p2230 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4831 := h105445;
    let u8 : (¬ p5660) := (Or.elim h94402 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115883 (p2331 p2881 p3323 p3425 p3461 p4253 p4789 p5660 p6172 : Prop)
    (h105646 : p4789)
    (h97239 : (¬ p5660) ∨ (¬ p4253) ∨ p3461 ∨ p2331 ∨ p3425 ∨ (¬ p2881) ∨ (¬ p4789) ∨ p3323)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ p3323 ∨ p3461 ∨ p2331 ∨ (¬ p2881) ∨ p3425 ∨ (¬ p4253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    let u8 : (¬ p5660) := (Or.elim h97239 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115884 (p2254 p2901 p2946 p3093 p3319 p3461 p4831 p5660 p6172 : Prop)
    (h105366 : p2254)
    (h105445 : p4831)
    (h99090 : (¬ p5660) ∨ p2946 ∨ (¬ p3319) ∨ (¬ p4831) ∨ (¬ p3461) ∨ (¬ p3093) ∨ p2901 ∨ (¬ p2254))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ p2901 ∨ (¬ p3093) ∨ (¬ p3461) ∨ (¬ p3319) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4831 := h105445;
    let u8 : (¬ p5660) := (Or.elim h99090 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115885 (p2774 p2901 p2946 p3461 p3483 p4789 p4831 p5660 p6172 : Prop)
    (h105445 : p4831)
    (h105646 : p4789)
    (h99096 : (¬ p5660) ∨ (¬ p3483) ∨ (¬ p3461) ∨ (¬ p4831) ∨ p2901 ∨ (¬ p4789) ∨ p2946 ∨ (¬ p2774))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3461) ∨ p2946 ∨ (¬ p2774) ∨ p2901 ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4831 := h105445;
    let u7 : p4789 := h105646;
    let u8 : (¬ p5660) := (Or.elim h99096 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u3))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115886 (p2132 p2651 p2870 p3276 p3343 p4786 p4831 p5660 p6172 : Prop)
    (h106425 : p4786)
    (h105445 : p4831)
    (h99097 : (¬ p3343) ∨ (¬ p5660) ∨ (¬ p4786) ∨ p2870 ∨ (¬ p4831) ∨ (¬ p2651) ∨ (¬ p3276) ∨ p2132)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3276) ∨ (¬ p2651) ∨ p2132 ∨ p2870 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4831 := h105445;
    let u8 : (¬ p5660) := (Or.elim h99097 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u3 r6))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step115889 (p2295 p2383 p2668 p2787 p3362 p3389 p3868 p4556 p5660 p6172 : Prop)
    (h105399 : p4556)
    (h105374 : p2787)
    (h79266 : (¬ p3868) ∨ (¬ p5660) ∨ (¬ p2668) ∨ (¬ p3389) ∨ p2295 ∨ (¬ p2787) ∨ (¬ p3362) ∨ (¬ p4556) ∨ p2383)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3868) ∨ p2383 ∨ p2295 ∨ (¬ p3389) ∨ (¬ p2668) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4556 := h105399;
    let u8 : p2787 := h105374;
    let u9 : (¬ p5660) := (Or.elim h79266 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115891 (p2132 p2383 p2528 p2781 p2870 p3266 p4432 p4831 p5660 p6172 : Prop)
    (h105445 : p4831)
    (h86709 : (¬ p2528) ∨ p2870 ∨ (¬ p2781) ∨ (¬ p4831) ∨ (¬ p3266) ∨ (¬ p2383) ∨ p2132 ∨ (¬ p5660) ∨ (¬ p4432))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3266) ∨ (¬ p2528) ∨ (¬ p2383) ∨ p2132 ∨ p2870 ∨ (¬ p4432) ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4831 := h105445;
    let u9 : (¬ p5660) := (Or.elim h86709 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u6))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115892 (p2249 p2641 p2891 p2946 p3323 p3461 p4282 p4831 p5660 p6172 : Prop)
    (h106513 : p2249)
    (h105445 : p4831)
    (h92740 : (¬ p5660) ∨ (¬ p3323) ∨ (¬ p4831) ∨ (¬ p3461) ∨ p2946 ∨ (¬ p4282) ∨ (¬ p2249) ∨ (¬ p2641) ∨ p2891)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p2641) ∨ (¬ p3461) ∨ (¬ p3323) ∨ p2946 ∨ (¬ p4282) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2249 := h106513;
    let u8 : p4831 := h105445;
    let u9 : (¬ p5660) := (Or.elim h92740 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u6 r7))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115895 (p2252 p2608 p2750 p2901 p2946 p3707 p3830 p4831 p5660 p6172 : Prop)
    (h106345 : p2750)
    (h105445 : p4831)
    (h99100 : (¬ p3830) ∨ (¬ p5660) ∨ (¬ p4831) ∨ (¬ p2750) ∨ p2901 ∨ (¬ p3707) ∨ p2608 ∨ (¬ p2252) ∨ p2946)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3830) ∨ (¬ p3707) ∨ p2608 ∨ p2946 ∨ p2901 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p4831 := h105445;
    let u9 : (¬ p5660) := (Or.elim h99100 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step115898 (p2132 p2246 p2744 p2870 p3166 p3256 p3266 p3366 p4831 p5660 p6172 : Prop)
    (h106503 : p2744)
    (h105445 : p4831)
    (h86711 : (¬ p5660) ∨ p2132 ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p2246) ∨ (¬ p3166) ∨ (¬ p4831) ∨ (¬ p3366) ∨ (¬ p3256) ∨ p2870)
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3256) ∨ (¬ p3266) ∨ p2870 ∨ p2132 ∨ (¬ p3166) ∨ (¬ p3366) ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4831 := h105445;
    let u10 : (¬ p5660) := (Or.elim h86711 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (u3 r8))))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115899 (p2132 p2246 p2331 p2744 p2870 p3323 p3366 p3461 p4831 p5660 p6172 : Prop)
    (h106503 : p2744)
    (h105445 : p4831)
    (h86713 : (¬ p5660) ∨ (¬ p2246) ∨ (¬ p2331) ∨ p2870 ∨ (¬ p3323) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2132 ∨ (¬ p3461) ∨ (¬ p4831))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p2331) ∨ p2870 ∨ (¬ p3461) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p2246) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4831 := h105445;
    let u10 : (¬ p5660) := (Or.elim h86713 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115901 (p2753 p2881 p3093 p3362 p3389 p3707 p3830 p3868 p4870 p5660 p6172 : Prop)
    (h91358 : (¬ p5660) ∨ p3707 ∨ (¬ p3868) ∨ (¬ p2881) ∨ (¬ p4870) ∨ (¬ p3362) ∨ (¬ p2753) ∨ p3830 ∨ (¬ p3389) ∨ (¬ p3093))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3868) ∨ (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3389) ∨ p3707 ∨ p3830 ∨ (¬ p3362) ∨ (¬ p2881) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5660) := (Or.elim h91358 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u3))))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115903 (p2651 p2957 p3051 p3136 p3276 p3333 p4343 p4790 p4831 p5660 p6172 : Prop)
    (h106424 : p4790)
    (h105445 : p4831)
    (h95639 : p3136 ∨ (¬ p3333) ∨ p3051 ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p3276) ∨ (¬ p5660) ∨ (¬ p4831) ∨ (¬ p2651) ∨ (¬ p2957))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3276) ∨ p3136 ∨ (¬ p2651) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p4343) ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4790 := h106424;
    let u9 : p4831 := h105445;
    let u10 : (¬ p5660) := (Or.elim h95639 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115905 (p2573 p2870 p2946 p3136 p3366 p3461 p3519 p3564 p4236 p5660 p6172 : Prop)
    (h112653 : (¬ p3136) ∨ (¬ p3564) ∨ (¬ p3461) ∨ p2946 ∨ p2870 ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p5660))
    (h115826 : p6172 ∨ p5660)
    : p6172 ∨ (¬ p3136) ∨ (¬ p3564) ∨ (¬ p3461) ∨ p2946 ∨ p2870 ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5660) := (Or.elim h112653 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => r8))))))))))))))))));
    (Or.elim h115826 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step115908 (p4129 p4253 p4344 p6172 : Prop)
    (h6599 : (¬ p4129) ∨ p4253 ∨ (¬ p4344))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p4253 ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4253) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4129) := (Or.elim h6599 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h115825 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115910 (p4129 p4283 p4372 p6172 : Prop)
    (h6695 : (¬ p4129) ∨ (¬ p4283) ∨ (¬ p4372))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4372) ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4129) := (Or.elim h6695 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h115825 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115911 (p2911 p3051 p4129 p5503 p6172 : Prop)
    (h46564 : (¬ p2911) ∨ (¬ p3051) ∨ (¬ p4129) ∨ (¬ p5503))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p5503) ∨ (¬ p3051) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4129) := (Or.elim h46564 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115912 (p2230 p3389 p4129 p5503 p6172 : Prop)
    (h76562 : (¬ p5503) ∨ (¬ p4129) ∨ p3389 ∨ (¬ p2230))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p5503) ∨ p3389 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4129) := (Or.elim h76562 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115913 (p2881 p3309 p4129 p4260 p6172 : Prop)
    (h80268 : (¬ p4260) ∨ (¬ p4129) ∨ p2881 ∨ p3309)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4260) ∨ p2881 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4129) := (Or.elim h80268 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115915 (p2241 p2901 p2992 p4129 p6172 : Prop)
    (h46087 : (¬ p2241) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4129))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p2992) ∨ (¬ p2241) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4129) := (Or.elim h46087 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h115825 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115918 (p2619 p4129 p4136 p4423 p4904 p6172 : Prop)
    (h61871 : (¬ p2619) ∨ (¬ p4129) ∨ (¬ p4136) ∨ (¬ p4423) ∨ (¬ p4904))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4423) ∨ (¬ p4136) ∨ (¬ p2619) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h61871 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115919 (p2427 p4129 p4136 p4423 p4882 p6172 : Prop)
    (h105453 : p4882)
    (h64498 : (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4136) ∨ (¬ p4423) ∨ (¬ p4882))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4423) ∨ (¬ p4136) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    let u5 : (¬ p4129) := (Or.elim h64498 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115920 (p2187 p2553 p3872 p4129 p4260 p6172 : Prop)
    (h75314 : (¬ p4129) ∨ (¬ p4260) ∨ p2187 ∨ (¬ p3872) ∨ p2553)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4260) ∨ (¬ p3872) ∨ p2187 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h75314 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115921 (p2122 p2187 p3872 p4129 p4260 p6172 : Prop)
    (h75316 : (¬ p4260) ∨ (¬ p4129) ∨ p2187 ∨ p2122 ∨ (¬ p3872))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4260) ∨ p2187 ∨ (¬ p3872) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h75316 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115923 (p2210 p2881 p3554 p4129 p4442 p6172 : Prop)
    (h75538 : (¬ p4129) ∨ (¬ p4442) ∨ p2881 ∨ p2210 ∨ (¬ p3554))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4442) ∨ p2210 ∨ p2881 ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h75538 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115924 (p2427 p4129 p4386 p4391 p4702 p6172 : Prop)
    (h106079 : p4702)
    (h54274 : (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) ∨ (¬ p4702))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p2427) ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    let u5 : (¬ p4129) := (Or.elim h54274 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115926 (p3051 p3115 p4129 p4386 p4391 p6172 : Prop)
    (h47483 : (¬ p3051) ∨ (¬ p3115) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p4386) ∨ (¬ p3115) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h47483 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115927 (p2230 p2441 p3246 p4129 p5503 p6172 : Prop)
    (h80280 : (¬ p4129) ∨ (¬ p5503) ∨ (¬ p2441) ∨ p2230 ∨ p3246)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p5503) ∨ p2230 ∨ (¬ p2441) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h80280 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115928 (p2192 p3554 p4129 p4442 p4555 p6172 : Prop)
    (h105542 : p4555)
    (h41584 : (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4555))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4442) ∨ (¬ p2192) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    let u5 : (¬ p4129) := (Or.elim h41584 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115930 (p2807 p3246 p4129 p4236 p4391 p6172 : Prop)
    (h80291 : (¬ p4129) ∨ (¬ p4236) ∨ p3246 ∨ p2807 ∨ (¬ p4391))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p4236) ∨ p2807 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h80291 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115933 (p2177 p2891 p4129 p4260 p4365 p6172 : Prop)
    (h45761 : (¬ p2177) ∨ (¬ p2891) ∨ (¬ p4129) ∨ (¬ p4260) ∨ (¬ p4365))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4260) ∨ (¬ p2891) ∨ (¬ p4365) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h45761 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115935 (p2441 p2870 p4129 p4885 p5503 p6172 : Prop)
    (h61645 : (¬ p2441) ∨ (¬ p2870) ∨ (¬ p4129) ∨ (¬ p4885) ∨ (¬ p5503))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p5503) ∨ (¬ p4885) ∨ (¬ p2441) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h61645 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115937 (p2373 p2427 p2437 p4129 p4391 p6172 : Prop)
    (h113988 : p2437 ∨ (¬ p4391) ∨ (¬ p4129) ∨ p2373 ∨ (¬ p2427))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2437 ∨ (¬ p4391) ∨ p2373 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h113988 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115938 (p2881 p2901 p3156 p4129 p5564 p6172 : Prop)
    (h114460 : p2881 ∨ (¬ p5564) ∨ (¬ p4129) ∨ p3156 ∨ (¬ p2901))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2881 ∨ (¬ p5564) ∨ p3156 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h114460 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115939 (p2220 p2881 p3051 p4129 p5564 p6172 : Prop)
    (h114463 : p2881 ∨ (¬ p5564) ∨ (¬ p4129) ∨ p2220 ∨ (¬ p3051))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2881 ∨ (¬ p5564) ∨ p2220 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4129) := (Or.elim h114463 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115940 (p2187 p2307 p2577 p3872 p4129 p4260 p6172 : Prop)
    (h75317 : (¬ p4260) ∨ (¬ p4129) ∨ p2307 ∨ (¬ p2577) ∨ (¬ p3872) ∨ p2187)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4260) ∨ p2307 ∨ (¬ p2577) ∨ (¬ p3872) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4129) := (Or.elim h75317 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115944 (p2363 p3146 p4119 p4129 p4138 p5564 p6172 : Prop)
    (h80270 : (¬ p4129) ∨ (¬ p5564) ∨ p3146 ∨ (¬ p4138) ∨ (¬ p4119) ∨ (¬ p2363))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p5564) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p4138) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4129) := (Or.elim h80270 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115945 (p2166 p3554 p3872 p4129 p4442 p4509 p6172 : Prop)
    (h105392 : p4509)
    (h61885 : (¬ p2166) ∨ (¬ p3554) ∨ (¬ p3872) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4509))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4442) ∨ (¬ p3872) ∨ (¬ p2166) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    let u6 : (¬ p4129) := (Or.elim h61885 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115948 (p2881 p2957 p2992 p4129 p4372 p4984 p6172 : Prop)
    (h80296 : (¬ p4129) ∨ (¬ p4372) ∨ (¬ p2957) ∨ (¬ p4984) ∨ p2881 ∨ p2992)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4372) ∨ (¬ p2957) ∨ p2992 ∨ (¬ p4984) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4129) := (Or.elim h80296 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115952 (p2761 p2850 p2870 p2982 p3246 p4129 p6172 : Prop)
    (h115121 : p2850 ∨ p3246 ∨ (¬ p2761) ∨ (¬ p4129) ∨ p2982 ∨ (¬ p2870))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2850 ∨ p3246 ∨ (¬ p2761) ∨ p2982 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4129) := (Or.elim h115121 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115960 (p2881 p3193 p3276 p3379 p3425 p4129 p4423 p4736 p6172 : Prop)
    (h105431 : p4736)
    (h75070 : (¬ p4423) ∨ (¬ p4129) ∨ (¬ p3425) ∨ p2881 ∨ (¬ p4736) ∨ p3193 ∨ (¬ p3276) ∨ (¬ p3379))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p4423) ∨ (¬ p3425) ∨ (¬ p3276) ∨ p3193 ∨ p2881 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : (¬ p4129) := (Or.elim h75070 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115964 (p2132 p2470 p2528 p2870 p3266 p4129 p4729 p4826 p6172 : Prop)
    (h105444 : p4826)
    (h105429 : p4729)
    (h79595 : (¬ p4129) ∨ p3266 ∨ (¬ p4826) ∨ p2470 ∨ p2528 ∨ (¬ p2870) ∨ (¬ p4729) ∨ (¬ p2132))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p2132) ∨ p3266 ∨ (¬ p2870) ∨ p2470 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4826 := h105444;
    let u7 : p4729 := h105429;
    let u8 : (¬ p4129) := (Or.elim h79595 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115965 (p2210 p2254 p2651 p2891 p3276 p3343 p4129 p4826 p6172 : Prop)
    (h105366 : p2254)
    (h105444 : p4826)
    (h80271 : (¬ p4129) ∨ p3343 ∨ (¬ p2254) ∨ p2651 ∨ p3276 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4826))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3276 ∨ (¬ p2210) ∨ p2651 ∨ (¬ p2891) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h80271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115966 (p2132 p2870 p3073 p3266 p3449 p4129 p4733 p4826 p6172 : Prop)
    (h105430 : p4733)
    (h105444 : p4826)
    (h80276 : (¬ p4129) ∨ p3266 ∨ (¬ p4826) ∨ p3449 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p4733) ∨ p3073)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3073 ∨ p3266 ∨ (¬ p2870) ∨ p3449 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h80276 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u1 r6))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115970 (p2210 p2254 p2891 p3166 p3256 p3266 p4129 p4826 p6172 : Prop)
    (h105366 : p2254)
    (h105444 : p4826)
    (h80294 : p3266 ∨ (¬ p4129) ∨ (¬ p2254) ∨ (¬ p2891) ∨ p3256 ∨ (¬ p4826) ∨ p3166 ∨ (¬ p2210))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3166 ∨ (¬ p2891) ∨ (¬ p2210) ∨ p3256 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h80294 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u3))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115971 (p2210 p2598 p2891 p3276 p4129 p4736 p4826 p5160 p6172 : Prop)
    (h105431 : p4736)
    (h105444 : p4826)
    (h80300 : p3276 ∨ (¬ p5160) ∨ (¬ p4129) ∨ (¬ p2210) ∨ (¬ p4826) ∨ (¬ p4736) ∨ (¬ p2891) ∨ p2598)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p2210) ∨ (¬ p2891) ∨ p3276 ∨ (¬ p5160) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h80300 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115973 (p2774 p2901 p2946 p3461 p3917 p4129 p4786 p4826 p6172 : Prop)
    (h106425 : p4786)
    (h105444 : p4826)
    (h86482 : (¬ p4129) ∨ p3461 ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4826) ∨ (¬ p3917) ∨ (¬ p4786) ∨ p2774)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3461 ∨ (¬ p3917) ∨ (¬ p2901) ∨ (¬ p2946) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h86482 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115974 (p2132 p2870 p3193 p3276 p3379 p4129 p4733 p4826 p6172 : Prop)
    (h105430 : p4733)
    (h105444 : p4826)
    (h90765 : (¬ p3193) ∨ p3276 ∨ (¬ p4129) ∨ (¬ p4826) ∨ (¬ p2870) ∨ p3379 ∨ (¬ p4733) ∨ (¬ p2132))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ (¬ p3193) ∨ (¬ p2870) ∨ p3276 ∨ p3379 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h90765 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115975 (p2098 p2230 p2427 p3266 p3609 p4129 p4419 p4826 p6172 : Prop)
    (h105444 : p4826)
    (h97193 : (¬ p4129) ∨ (¬ p2427) ∨ p3266 ∨ (¬ p4826) ∨ p2098 ∨ (¬ p4419) ∨ p3609 ∨ (¬ p2230))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3266 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3609 ∨ p2098 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4826 := h105444;
    let u8 : (¬ p4129) := (Or.elim h97193 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115976 (p2230 p2427 p2608 p3519 p3599 p3670 p3830 p4129 p6172 : Prop)
    (h108939 : p3599 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3830 ∨ (¬ p3519) ∨ p3670 ∨ (¬ p4129) ∨ (¬ p2608))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3599 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3830 ∨ (¬ p3519) ∨ p3670 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4129) := (Or.elim h108939 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115980 (p2230 p2331 p2850 p2870 p3323 p3362 p3461 p4129 p6172 : Prop)
    (h115136 : p2850 ∨ p3323 ∨ p3461 ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2870) ∨ (¬ p3362) ∨ (¬ p4129))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2850 ∨ p3323 ∨ p3461 ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2870) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4129) := (Or.elim h115136 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => r6))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115982 (p2132 p2573 p2753 p2870 p3347 p3461 p3564 p4129 p4826 p6172 : Prop)
    (h105444 : p4826)
    (h90623 : (¬ p4129) ∨ (¬ p2753) ∨ p3564 ∨ p3461 ∨ (¬ p3347) ∨ (¬ p2132) ∨ (¬ p4826) ∨ p2573 ∨ (¬ p2870))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3461 ∨ (¬ p2132) ∨ (¬ p2870) ∨ p2573 ∨ p3564 ∨ (¬ p2753) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4826 := h105444;
    let u9 : (¬ p4129) := (Or.elim h90623 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115987 (p2088 p2255 p2891 p2946 p3177 p3189 p3266 p3412 p4129 p4826 p6172 : Prop)
    (h105367 : p2255)
    (h105444 : p4826)
    (h80269 : (¬ p4129) ∨ p3266 ∨ (¬ p4826) ∨ (¬ p2255) ∨ p3189 ∨ p2088 ∨ (¬ p2891) ∨ (¬ p3177) ∨ (¬ p3412) ∨ (¬ p2946))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3266 ∨ (¬ p3177) ∨ p2088 ∨ p3189 ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4129) := (Or.elim h80269 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115991 (p2132 p2252 p2651 p2750 p2753 p2870 p3276 p3343 p4129 p4826 p6172 : Prop)
    (h106345 : p2750)
    (h105444 : p4826)
    (h90732 : p3276 ∨ p3343 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4826) ∨ (¬ p4129) ∨ (¬ p2870) ∨ p2651 ∨ (¬ p2753) ∨ (¬ p2132))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3276 ∨ (¬ p2132) ∨ (¬ p2870) ∨ p3343 ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4129) := (Or.elim h90732 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u2))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115992 (p2132 p2252 p2750 p2753 p2870 p3166 p3256 p3266 p4129 p4826 p6172 : Prop)
    (h106345 : p2750)
    (h105444 : p4826)
    (h90793 : (¬ p4129) ∨ (¬ p2753) ∨ p3256 ∨ (¬ p2252) ∨ (¬ p2750) ∨ p3266 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p4826) ∨ p3166)
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3266 ∨ p3166 ∨ (¬ p2132) ∨ (¬ p2870) ∨ p3256 ∨ (¬ p2753) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4129) := (Or.elim h90793 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115994 (p2230 p2427 p2696 p2753 p3005 p3519 p4129 p4376 p5560 p5600 p6172 : Prop)
    (h106320 : p4376)
    (h106188 : p5560)
    (h99781 : p2753 ∨ (¬ p5600) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p5560) ∨ (¬ p2427) ∨ p3005 ∨ (¬ p2230) ∨ (¬ p4129) ∨ (¬ p4376))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p2753 ∨ p3005 ∨ (¬ p2427) ∨ p2696 ∨ (¬ p3519) ∨ (¬ p5600) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2753) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5560 := h106188;
    let u10 : (¬ p4129) := (Or.elim h99781 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115995 (p2230 p2427 p2753 p3005 p3073 p3609 p4129 p4419 p4436 p5600 p6172 : Prop)
    (h110593 : p3005 ∨ p3073 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4129) ∨ (¬ p5600) ∨ (¬ p4436) ∨ (¬ p4419))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3005 ∨ p3073 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p5600) ∨ (¬ p4436) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4129) := (Or.elim h110593 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step115999 (p2230 p2427 p2696 p2753 p3519 p3590 p3599 p3670 p4129 p4749 p4826 p6172 : Prop)
    (h105432 : p4749)
    (h105444 : p4826)
    (h76228 : (¬ p4129) ∨ (¬ p2753) ∨ (¬ p2427) ∨ (¬ p4826) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p2696) ∨ p3670 ∨ (¬ p4749) ∨ p3599 ∨ (¬ p2230))
    (h115825 : p4129 ∨ (¬ p6172))
    : (¬ p6172) ∨ p3670 ∨ p3599 ∨ (¬ p2230) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4749 := h105432;
    let u10 : p4826 := h105444;
    let u11 : (¬ p4129) := (Or.elim h76228 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (r9 u3))))))))))))))))))))));
    (Or.elim h115825 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116005 (p2363 p2528 p3990 p4157 : Prop)
    (h111894 : (¬ p2363) ∨ (¬ p4157) ∨ p2528 ∨ (¬ p3990))
    (h90097 : p3990 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p4157) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3990) := (Or.elim h111894 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h90097 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116008 (p2630 p3136 p3413 p4392 : Prop)
    (h115330 : p3136 ∨ (¬ p4392) ∨ (¬ p2630) ∨ (¬ p3413))
    (h101558 : p4392 ∨ p3136)
    : p3136 ∨ (¬ p2630) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4392) := (Or.elim h115330 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h101558 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116009 (p2807 p2992 p2996 p3136 p4392 : Prop)
    (h115364 : p3136 ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p4392) ∨ (¬ p2992))
    (h101558 : p4392 ∨ p3136)
    : p3136 ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4392) := (Or.elim h115364 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101558 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116010 (p2341 p2717 p3577 p4403 : Prop)
    (h114672 : (¬ p2341) ∨ p2717 ∨ (¬ p3577) ∨ (¬ p4403))
    (h96446 : p4403 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2717 ∨ (¬ p3577) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4403) := (Or.elim h114672 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96446 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116016 (p3619 p5351 p6092 : Prop)
    (h110385 : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p3619))
    (h9198 : p3619 ∨ (¬ p5351))
    : (¬ p5351) ∨ (¬ p6092) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3619) := (Or.elim h110385 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h9198 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116017 (p3619 p5351 p6092 : Prop)
    (h110388 : p6092 ∨ p5351 ∨ (¬ p3619))
    (h13659 : p3619 ∨ p6092)
    : p6092 ∨ p5351 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5351) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3619) := (Or.elim h110388 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h13659 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116018 (p4398 p5351 p6092 : Prop)
    (h116016 : (¬ p5351) ∨ (¬ p6092))
    (h108725 : p5351 ∨ p4398)
    : p4398 ∨ (¬ p6092) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4398) := (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5351) := (Or.elim h116016 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108725 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116019 (p4234 p5351 p6092 : Prop)
    (h116016 : (¬ p5351) ∨ (¬ p6092))
    (h108726 : p5351 ∨ p4234)
    : p4234 ∨ (¬ p6092) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4234) := (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5351) := (Or.elim h116016 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108726 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116020 (p4232 p5351 p6092 : Prop)
    (h116016 : (¬ p5351) ∨ (¬ p6092))
    (h108727 : p5351 ∨ p4232)
    : p4232 ∨ (¬ p6092) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4232) := (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5351) := (Or.elim h116016 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108727 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116021 (p4233 p5351 p6092 : Prop)
    (h9196 : p4233 ∨ (¬ p5351))
    (h116017 : p6092 ∨ p5351)
    : p6092 ∨ p4233 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4233) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5351) := (Or.elim h9196 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116017 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116022 (p3619 p5351 p6092 : Prop)
    (h9198 : p3619 ∨ (¬ p5351))
    (h116017 : p6092 ∨ p5351)
    : p6092 ∨ p3619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3619) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5351) := (Or.elim h9198 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116017 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116023 (p2753 p3599 p5351 p6092 : Prop)
    (h110386 : (¬ p5351) ∨ (¬ p2753) ∨ p3599)
    (h116017 : p6092 ∨ p5351)
    : p6092 ∨ (¬ p2753) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5351) := (Or.elim h110386 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h116017 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step116028 (p2098 p3609 p4234 p4398 p6092 : Prop)
    (h109458 : (¬ p3609) ∨ (¬ p4234) ∨ (¬ p4398) ∨ (¬ p2098))
    (h116019 : p4234 ∨ (¬ p6092))
    : (¬ p6092) ∨ (¬ p3609) ∨ (¬ p4398) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4398 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4234) := (Or.elim h109458 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116019 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116035 (p2098 p3609 p4398 p6092 : Prop)
    (h116028 : (¬ p6092) ∨ (¬ p3609) ∨ (¬ p4398) ∨ (¬ p2098))
    (h116018 : p4398 ∨ (¬ p6092))
    : (¬ p6092) ∨ (¬ p3609) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4398) := (Or.elim h116028 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h116018 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116042 (p2341 p2881 p3960 p4283 : Prop)
    (h115588 : p2341 ∨ (¬ p4283) ∨ (¬ p3960) ∨ (¬ p2881))
    (h89806 : p3960 ∨ p2341)
    : p2341 ∨ (¬ p4283) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3960) := (Or.elim h115588 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h89806 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116044 (p2341 p2717 p3959 p3960 : Prop)
    (h115590 : p2341 ∨ (¬ p2717) ∨ (¬ p3959) ∨ (¬ p3960))
    (h89806 : p3960 ∨ p2341)
    : p2341 ∨ (¬ p2717) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3960) := (Or.elim h115590 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h89806 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116050 (p4075 p5648 p6170 : Prop)
    (h109088 : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170))
    (h10007 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p6170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6170 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4075) := (Or.elim h109088 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h10007 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116051 (p4075 p5648 p6170 : Prop)
    (h109090 : p6170 ∨ (¬ p4075) ∨ p5648)
    (h14757 : p4075 ∨ p6170)
    : p6170 ∨ p5648 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5648) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4075) := (Or.elim h109090 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14757 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116052 (p4075 p5648 p6170 : Prop)
    (h116050 : (¬ p5648) ∨ (¬ p6170))
    (h14757 : p4075 ∨ p6170)
    : p4075 ∨ (¬ p5648) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4075) := (fun h => hn (Or.inl h));
    let u1 : p5648 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6170) := (Or.elim h116050 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h14757 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116053 (p4442 p5648 p6170 : Prop)
    (h108875 : (¬ p6170) ∨ p4442)
    (h116051 : p6170 ∨ p5648)
    : p5648 ∨ p4442 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5648) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4442) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6170) := (Or.elim h108875 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h116051 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116056 (p3546 p4372 p5648 p6170 : Prop)
    (h109091 : p6170 ∨ (¬ p4372) ∨ (¬ p3546))
    (h116050 : (¬ p5648) ∨ (¬ p6170))
    : (¬ p5648) ∨ (¬ p4372) ∨ (¬ p3546) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p6170 := (Or.elim h109091 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h116050 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step116061 (p2685 p2797 p4075 p4391 p5648 : Prop)
    (h92294 : (¬ p4075) ∨ (¬ p4391) ∨ p2685 ∨ (¬ p2797))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p4391) ∨ p2685 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4075) := (Or.elim h92294 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116062 (p2417 p3399 p4075 p5503 p5648 : Prop)
    (h46509 : (¬ p2417) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5503))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p2417) ∨ (¬ p5503) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4075) := (Or.elim h46509 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116066 (p2881 p3399 p4075 p5648 p6172 : Prop)
    (h115838 : p6172 ∨ (¬ p4075) ∨ (¬ p2881) ∨ (¬ p3399))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ (¬ p2881) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4075) := (Or.elim h115838 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116068 (p2901 p3115 p4075 p5648 p6172 : Prop)
    (h115844 : p6172 ∨ (¬ p4075) ∨ (¬ p3115) ∨ p2901)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ (¬ p3115) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4075) := (Or.elim h115844 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116070 (p2427 p4075 p4431 p5648 p6172 : Prop)
    (h115847 : p6172 ∨ (¬ p4075) ∨ (¬ p4431) ∨ p2427)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ (¬ p4431) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4075) := (Or.elim h115847 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116077 (p2396 p2807 p3032 p4075 p4260 p5648 : Prop)
    (h45577 : (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p4075) ∨ (¬ p4260))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p4260) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4075) := (Or.elim h45577 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116079 (p2630 p2685 p4075 p4155 p4372 p5648 : Prop)
    (h101804 : (¬ p4075) ∨ (¬ p4372) ∨ p2685 ∨ (¬ p2630) ∨ (¬ p4155))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p4372) ∨ (¬ p2630) ∨ (¬ p4155) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4075) := (Or.elim h101804 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116084 (p2363 p3073 p3527 p4075 p4372 p5648 : Prop)
    (h112238 : p3527 ∨ (¬ p4075) ∨ (¬ p4372) ∨ (¬ p2363) ∨ p3073)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3527 ∨ (¬ p4372) ∨ (¬ p2363) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4075) := (Or.elim h112238 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116085 (p3073 p3146 p3527 p4075 p4372 p5648 : Prop)
    (h112241 : p3527 ∨ (¬ p4372) ∨ (¬ p4075) ∨ p3073 ∨ (¬ p3146))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3527 ∨ (¬ p4372) ∨ p3073 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4075) := (Or.elim h112241 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116087 (p2901 p4075 p4338 p4452 p5648 p6172 : Prop)
    (h115864 : p6172 ∨ (¬ p4075) ∨ p2901 ∨ (¬ p4338) ∨ (¬ p4452))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ p2901 ∨ (¬ p4338) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4075) := (Or.elim h115864 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116093 (p2122 p2187 p4075 p4185 p4423 p4427 p5648 : Prop)
    (h111835 : p2122 ∨ (¬ p4423) ∨ (¬ p2187) ∨ (¬ p4185) ∨ (¬ p4427) ∨ (¬ p4075))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2122 ∨ (¬ p4423) ∨ (¬ p2187) ∨ (¬ p4185) ∨ (¬ p4427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4075) := (Or.elim h111835 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116096 (p2819 p2829 p4075 p4452 p4710 p5503 p5648 : Prop)
    (h113625 : p2829 ∨ (¬ p5503) ∨ (¬ p4075) ∨ (¬ p4710) ∨ (¬ p4452) ∨ p2819)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2829 ∨ (¬ p5503) ∨ (¬ p4710) ∨ (¬ p4452) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4075) := (Or.elim h113625 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116097 (p2264 p3146 p3256 p4075 p4391 p4431 p5648 : Prop)
    (h115279 : (¬ p2264) ∨ (¬ p4391) ∨ (¬ p4075) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p4431))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p2264) ∨ (¬ p4391) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4075) := (Or.elim h115279 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116102 (p2187 p2406 p2922 p4075 p4204 p5648 p6172 : Prop)
    (h115872 : p6172 ∨ (¬ p2922) ∨ (¬ p4075) ∨ (¬ p4204) ∨ p2406 ∨ (¬ p2187))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ (¬ p2922) ∨ (¬ p4204) ∨ p2406 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4075) := (Or.elim h115872 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116108 (p2132 p2187 p3366 p3687 p4075 p4204 p5648 p6172 : Prop)
    (h115873 : p6172 ∨ (¬ p4075) ∨ (¬ p4204) ∨ (¬ p3366) ∨ (¬ p2187) ∨ p2132 ∨ (¬ p3687))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p6172 ∨ (¬ p4204) ∨ (¬ p3366) ∨ (¬ p2187) ∨ p2132 ∨ (¬ p3687) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6172) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4075) := (Or.elim h115873 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116110 (p2470 p2528 p2608 p3266 p3347 p3399 p4075 p4826 p5648 : Prop)
    (h105444 : p4826)
    (h79591 : (¬ p4075) ∨ p3266 ∨ p2608 ∨ (¬ p4826) ∨ (¬ p3347) ∨ p2528 ∨ p2470 ∨ (¬ p3399))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3266 ∨ p2470 ∨ (¬ p3399) ∨ p2608 ∨ p2528 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4826 := h105444;
    let u8 : (¬ p4075) := (Or.elim h79591 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u3))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116112 (p2573 p2608 p3347 p3399 p3461 p3564 p4075 p4826 p5648 : Prop)
    (h105444 : p4826)
    (h97268 : (¬ p4075) ∨ p3461 ∨ p2608 ∨ (¬ p4826) ∨ p3564 ∨ (¬ p3399) ∨ p2573 ∨ (¬ p3347))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3461 ∨ (¬ p3399) ∨ p2573 ∨ p2608 ∨ p3564 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4826 := h105444;
    let u8 : (¬ p4075) := (Or.elim h97268 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116113 (p2220 p2437 p3016 p3146 p3266 p3399 p4075 p4391 p5648 : Prop)
    (h114031 : p2437 ∨ p2220 ∨ p3146 ∨ (¬ p3016) ∨ (¬ p3399) ∨ p3266 ∨ (¬ p4075) ∨ (¬ p4391))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2437 ∨ p2220 ∨ p3146 ∨ (¬ p3016) ∨ (¬ p3399) ∨ p3266 ∨ (¬ p4391) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4075) := (Or.elim h114031 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116118 (p2156 p2608 p3125 p3399 p3461 p3645 p4075 p4826 p4877 p5648 : Prop)
    (h105451 : p4877)
    (h105444 : p4826)
    (h85502 : (¬ p4075) ∨ p2608 ∨ p3125 ∨ p3461 ∨ (¬ p3399) ∨ p2156 ∨ (¬ p4877) ∨ (¬ p4826) ∨ (¬ p3645))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3125 ∨ p2156 ∨ p3461 ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4877 := h105451;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h85502 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u6))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116119 (p2363 p2383 p2608 p3204 p3266 p3399 p4075 p4826 p4870 p5648 : Prop)
    (h105444 : p4826)
    (h88170 : (¬ p4075) ∨ p3266 ∨ (¬ p3399) ∨ p2363 ∨ p2383 ∨ (¬ p4826) ∨ (¬ p4870) ∨ p2608 ∨ (¬ p3204))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2363 ∨ p3266 ∨ p2383 ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3204) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h88170 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u6))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116121 (p2220 p2608 p3146 p3266 p3399 p3645 p4075 p4826 p4877 p5648 : Prop)
    (h105451 : p4877)
    (h105444 : p4826)
    (h92520 : (¬ p4075) ∨ p2608 ∨ (¬ p4877) ∨ p2220 ∨ (¬ p3399) ∨ p3146 ∨ p3266 ∨ (¬ p3645) ∨ (¬ p4826))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3146 ∨ (¬ p3399) ∨ p2608 ∨ p2220 ∨ (¬ p3645) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4877 := h105451;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h92520 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116122 (p2122 p2177 p2241 p2744 p2774 p3366 p3399 p4075 p5564 p5648 : Prop)
    (h106503 : p2744)
    (h93139 : (¬ p4075) ∨ (¬ p5564) ∨ (¬ p2744) ∨ p2241 ∨ p2177 ∨ (¬ p3399) ∨ (¬ p3366) ∨ p2122 ∨ p2774)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p5564) ∨ (¬ p3399) ∨ p2774 ∨ p2122 ∨ (¬ p3366) ∨ p2241 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : (¬ p4075) := (Or.elim h93139 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116123 (p2252 p2331 p2608 p2750 p3323 p3399 p3461 p4075 p4826 p5648 : Prop)
    (h106345 : p2750)
    (h105444 : p4826)
    (h97249 : (¬ p4075) ∨ p3461 ∨ p2608 ∨ (¬ p4826) ∨ (¬ p2750) ∨ (¬ p3399) ∨ p2331 ∨ (¬ p2252) ∨ p3323)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3461 ∨ (¬ p3399) ∨ p2608 ∨ p2331 ∨ p3323 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h97249 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u5 r7))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116127 (p2098 p3266 p3366 p3379 p3399 p3609 p4075 p4376 p4826 p5648 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h97271 : (¬ p4075) ∨ (¬ p3399) ∨ p3609 ∨ (¬ p4826) ∨ (¬ p3366) ∨ p2098 ∨ p3379 ∨ (¬ p4376) ∨ p3266)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3266 ∨ (¬ p3399) ∨ p3609 ∨ p2098 ∨ (¬ p3366) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h97271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u1 r7))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116128 (p2696 p3366 p3379 p3399 p3755 p4075 p4376 p4826 p5284 p5648 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h97545 : (¬ p4075) ∨ p3755 ∨ (¬ p4376) ∨ p3379 ∨ (¬ p3399) ∨ p2696 ∨ (¬ p5284) ∨ (¬ p4826) ∨ (¬ p3366))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p3399) ∨ (¬ p3366) ∨ p3379 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h97545 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116129 (p2098 p2241 p2744 p3266 p3366 p3399 p3609 p4075 p4826 p5648 : Prop)
    (h106503 : p2744)
    (h105444 : p4826)
    (h101626 : p3609 ∨ p2098 ∨ (¬ p2744) ∨ (¬ p4826) ∨ p3266 ∨ (¬ p3399) ∨ (¬ p3366) ∨ p2241 ∨ (¬ p4075))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3266 ∨ (¬ p3399) ∨ p3609 ∨ p2098 ∨ (¬ p3366) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4826 := h105444;
    let u9 : (¬ p4075) := (Or.elim h101626 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116133 (p2396 p2563 p2651 p2850 p2860 p3399 p3683 p4075 p4260 p5648 : Prop)
    (h111181 : p2850 ∨ (¬ p4075) ∨ (¬ p4260) ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p2563) ∨ p2651 ∨ (¬ p3683) ∨ p2860)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2850 ∨ (¬ p4260) ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p2563) ∨ p2651 ∨ (¬ p3683) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4075) := (Or.elim h111181 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116134 (p3005 p3166 p3266 p3366 p3379 p3399 p3609 p4075 p4236 p5648 : Prop)
    (h111387 : (¬ p3005) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p3166 ∨ p3609 ∨ p3266 ∨ (¬ p4236) ∨ (¬ p4075) ∨ p3379)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ (¬ p3005) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p3166 ∨ p3609 ∨ p3266 ∨ (¬ p4236) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4075) := (Or.elim h111387 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116136 (p2210 p2252 p2651 p2741 p3276 p3343 p3399 p4075 p4377 p4826 p5648 : Prop)
    (h106170 : p4377)
    (h105444 : p4826)
    (h75499 : (¬ p4075) ∨ p3276 ∨ (¬ p4826) ∨ p3343 ∨ (¬ p2741) ∨ p2210 ∨ p2651 ∨ (¬ p2252) ∨ (¬ p4377) ∨ (¬ p3399))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3276 ∨ p2210 ∨ (¬ p3399) ∨ p3343 ∨ (¬ p2252) ∨ (¬ p2741) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4075) := (Or.elim h75499 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3))))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116140 (p2241 p2363 p2383 p2744 p2778 p3266 p3366 p3399 p4075 p4826 p5648 : Prop)
    (h106503 : p2744)
    (h105444 : p4826)
    (h97255 : (¬ p4075) ∨ (¬ p4826) ∨ (¬ p2744) ∨ (¬ p3399) ∨ (¬ p3366) ∨ (¬ p2778) ∨ p2241 ∨ p2383 ∨ p2363 ∨ p3266)
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p2363 ∨ p2383 ∨ (¬ p3399) ∨ p2241 ∨ p3266 ∨ (¬ p3366) ∨ (¬ p2778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4075) := (Or.elim h97255 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u5 r8))))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116142 (p2210 p2252 p2651 p2750 p3276 p3343 p3371 p3399 p4075 p4826 p5648 : Prop)
    (h106345 : p2750)
    (h105444 : p4826)
    (h97266 : (¬ p4075) ∨ p3276 ∨ p2651 ∨ (¬ p3399) ∨ (¬ p2252) ∨ p3343 ∨ (¬ p3371) ∨ (¬ p2750) ∨ p2210 ∨ (¬ p4826))
    (h116052 : p4075 ∨ (¬ p5648))
    : (¬ p5648) ∨ p3343 ∨ (¬ p3399) ∨ p3276 ∨ p2651 ∨ p2210 ∨ (¬ p2252) ∨ (¬ p3371) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4075) := (Or.elim h97266 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h116052 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116149 (p3931 p5549 p6143 : Prop)
    (h108796 : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143))
    (h9709 : p3931 ∨ (¬ p5549))
    : (¬ p5549) ∨ (¬ p6143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6143 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3931) := (Or.elim h108796 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9709 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116150 (p3931 p5549 p6143 : Prop)
    (h108798 : p6143 ∨ (¬ p3931) ∨ p5549)
    (h14255 : p3931 ∨ p6143)
    : p6143 ∨ p5549 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6143) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5549) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3931) := (Or.elim h108798 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116151 (p3931 p5549 p6143 : Prop)
    (h116150 : p6143 ∨ p5549)
    (h9709 : p3931 ∨ (¬ p5549))
    : p3931 ∨ p6143 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3931) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6143) := (fun h => hn (Or.inr h));
    let u2 : p5549 := (Or.elim h116150 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h9709 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step116152 (p4391 p5549 p6143 : Prop)
    (h108515 : p5549 ∨ p4391)
    (h116149 : (¬ p5549) ∨ (¬ p6143))
    : (¬ p6143) ∨ p4391 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4391) := (fun h => hn (Or.inr h));
    let u2 : p5549 := (Or.elim h108515 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h116149 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step116156 (p3032 p4391 p4442 p6143 : Prop)
    (h37523 : (¬ p3032) ∨ (¬ p4391) ∨ p4442)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ p4442 ∨ (¬ p3032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4442) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4391) := (Or.elim h37523 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step116159 (p2807 p2911 p3868 p4391 p6143 : Prop)
    (h97217 : (¬ p3868) ∨ (¬ p4391) ∨ p2807 ∨ p2911)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3868) ∨ p2807 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4391) := (Or.elim h97217 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116160 (p2685 p4063 p4391 p4790 p6143 : Prop)
    (h106424 : p4790)
    (h101789 : (¬ p4391) ∨ (¬ p4063) ∨ (¬ p4790) ∨ p2685)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p4063) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4790 := h106424;
    let u4 : (¬ p4391) := (Or.elim h101789 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116163 (p2437 p3389 p3868 p4391 p6143 : Prop)
    (h113983 : p2437 ∨ (¬ p4391) ∨ (¬ p3868) ∨ (¬ p3389))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ p2437 ∨ (¬ p3868) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4391) := (Or.elim h113983 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116164 (p2427 p4386 p4391 p6143 p6172 : Prop)
    (h115924 : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p2427) ∨ (¬ p4386))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p6172) ∨ (¬ p2427) ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4391) := (Or.elim h115924 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116165 (p2685 p2797 p4391 p5648 p6143 : Prop)
    (h116061 : (¬ p5648) ∨ (¬ p4391) ∨ p2685 ∨ (¬ p2797))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p5648) ∨ p2685 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5648 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4391) := (Or.elim h116061 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116166 (p2274 p3791 p4067 p4391 p4564 p6143 : Prop)
    (h105401 : p4564)
    (h41143 : (¬ p2274) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4564))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    let u5 : (¬ p4391) := (Or.elim h41143 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116167 (p2668 p3791 p4067 p4391 p4405 p6143 : Prop)
    (h105512 : p4405)
    (h52635 : (¬ p2668) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4405))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3791) ∨ (¬ p2668) ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4391) := (Or.elim h52635 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116168 (p2449 p2696 p3819 p4063 p4391 p6143 : Prop)
    (h82915 : (¬ p3819) ∨ (¬ p4391) ∨ p2696 ∨ (¬ p2449) ∨ (¬ p4063))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p4063) ∨ p2696 ∨ (¬ p2449) ∨ (¬ p3819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h82915 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116170 (p2177 p2807 p3791 p4236 p4391 p6143 : Prop)
    (h98788 : (¬ p3791) ∨ (¬ p4391) ∨ (¬ p4236) ∨ p2177 ∨ p2807)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3791) ∨ (¬ p4236) ∨ p2177 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h98788 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116171 (p3032 p3399 p3449 p3527 p4391 p6143 : Prop)
    (h111041 : (¬ p3527) ∨ (¬ p4391) ∨ (¬ p3032) ∨ p3399 ∨ (¬ p3449))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3527) ∨ (¬ p3032) ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h111041 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116172 (p2437 p3016 p3741 p3868 p4391 p6143 : Prop)
    (h114009 : p2437 ∨ (¬ p4391) ∨ (¬ p3868) ∨ (¬ p3016) ∨ (¬ p3741))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ p2437 ∨ (¬ p3868) ∨ (¬ p3016) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h114009 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116173 (p2088 p2341 p2459 p4066 p4391 p6143 : Prop)
    (h114681 : (¬ p2341) ∨ (¬ p4391) ∨ (¬ p2088) ∨ p2459 ∨ (¬ p4066))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p2341) ∨ (¬ p2088) ∨ p2459 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h114681 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116176 (p3051 p3115 p4386 p4391 p6143 p6172 : Prop)
    (h115926 : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p4386) ∨ (¬ p3115) ∨ (¬ p3051))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p6172) ∨ (¬ p4386) ∨ (¬ p3115) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h115926 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116177 (p2807 p3246 p4236 p4391 p6143 p6172 : Prop)
    (h115930 : (¬ p6172) ∨ (¬ p4391) ∨ (¬ p4236) ∨ p2807 ∨ p3246)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p6172) ∨ (¬ p4236) ∨ p2807 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h115930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116178 (p2373 p2427 p2437 p4391 p6143 p6172 : Prop)
    (h115937 : (¬ p6172) ∨ p2437 ∨ (¬ p4391) ∨ p2373 ∨ (¬ p2427))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p6172) ∨ p2437 ∨ p2373 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4391) := (Or.elim h115937 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

end ElevenRUP
