import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step110909 (p2241 p2449 p2761 p2996 p4429 p5284 : Prop)
    (h99873 : (¬ p5284) ∨ p2241 ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p4429))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p5284) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4429) := (Or.elim h99873 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110910 (p2352 p2449 p3276 p3552 p4422 p4429 p5284 : Prop)
    (h93260 : (¬ p5284) ∨ (¬ p4422) ∨ (¬ p3552) ∨ (¬ p3276) ∨ (¬ p4429) ∨ p2352)
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p5284) ∨ (¬ p3552) ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4429) := (Or.elim h93260 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110911 (p2264 p2449 p2717 p3266 p4136 p4429 p5284 : Prop)
    (h93267 : (¬ p4429) ∨ (¬ p5284) ∨ (¬ p2264) ∨ (¬ p4136) ∨ p2717 ∨ (¬ p3266))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p5284) ∨ (¬ p2264) ∨ p2717 ∨ (¬ p3266) ∨ (¬ p4136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4429) := (Or.elim h93267 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110912 (p2396 p2449 p2761 p3579 p4276 p4429 p5284 : Prop)
    (h105516 : p4276)
    (h41080 : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4429) ∨ (¬ p5284))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p2761) ∨ (¬ p2396) ∨ (¬ p5284) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4276 := h105516;
    let u6 : (¬ p4429) := (Or.elim h41080 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110913 (p2383 p2449 p3552 p3767 p4036 p4429 p5284 : Prop)
    (h93305 : (¬ p5284) ∨ (¬ p3767) ∨ (¬ p4036) ∨ (¬ p4429) ∨ p2383 ∨ (¬ p3552))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3767) ∨ (¬ p3552) ∨ (¬ p5284) ∨ p2383 ∨ (¬ p4036) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4429) := (Or.elim h93305 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110916 (p2449 p2972 p2982 p3707 p4386 p4429 p5284 : Prop)
    (h110208 : p2972 ∨ (¬ p3707) ∨ (¬ p4386) ∨ (¬ p5284) ∨ (¬ p4429) ∨ (¬ p2982))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ p2972 ∨ (¬ p3707) ∨ (¬ p4386) ∨ (¬ p5284) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4429) := (Or.elim h110208 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110920 (p2192 p2210 p2254 p2449 p2761 p2807 p3125 p4429 p4621 p5284 : Prop)
    (h105366 : p2254)
    (h105407 : p4621)
    (h93298 : (¬ p5284) ∨ (¬ p2761) ∨ (¬ p4621) ∨ p2807 ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p2254) ∨ (¬ p4429))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p2761) ∨ (¬ p5284) ∨ (¬ p2192) ∨ (¬ p3125) ∨ (¬ p2210) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4621 := h105407;
    let u9 : (¬ p4429) := (Or.elim h93298 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110924 (p2249 p2449 p2573 p2656 p2727 p2761 p2807 p3564 p4429 p4621 p5284 : Prop)
    (h106513 : p2249)
    (h105407 : p4621)
    (h93276 : (¬ p5284) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2761) ∨ (¬ p2727) ∨ (¬ p2249) ∨ p2807 ∨ (¬ p4621) ∨ (¬ p4429) ∨ (¬ p3564))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p2761) ∨ (¬ p5284) ∨ p2807 ∨ (¬ p3564) ∨ (¬ p2656) ∨ (¬ p2573) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4621 := h105407;
    let u10 : (¬ p4429) := (Or.elim h93276 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110930 (p2383 p3654 p3990 p5379 : Prop)
    (h110546 : p3654 ∨ (¬ p3990) ∨ (¬ p5379) ∨ (¬ p2383))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p3990) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5379) := (Or.elim h110546 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110932 (p2307 p2553 p3125 p3654 p5379 : Prop)
    (h110551 : p3654 ∨ (¬ p2307) ∨ (¬ p3125) ∨ p2553 ∨ (¬ p5379))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p2307) ∨ (¬ p3125) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5379) := (Or.elim h110551 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110939 (p2122 p2449 p3483 p3516 p3654 p5379 : Prop)
    (h109545 : (¬ p3516) ∨ p2122 ∨ p2449 ∨ (¬ p5379) ∨ (¬ p3483))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p3516) ∨ p2122 ∨ p2449 ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5379) := (Or.elim h109545 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110941 (p2295 p3246 p3323 p3516 p3654 p5379 : Prop)
    (h109551 : (¬ p3516) ∨ p2295 ∨ (¬ p3323) ∨ (¬ p5379) ∨ p3246)
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p3516) ∨ p2295 ∨ (¬ p3323) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5379) := (Or.elim h109551 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110944 (p2088 p2819 p3146 p3483 p3654 p5379 : Prop)
    (h109903 : (¬ p2088) ∨ (¬ p3483) ∨ p2819 ∨ (¬ p5379) ∨ p3146)
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p2088) ∨ (¬ p3483) ∨ p2819 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5379) := (Or.elim h109903 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110948 (p2797 p3125 p3297 p3654 p3755 p4564 p5379 : Prop)
    (h105401 : p4564)
    (h92283 : p3755 ∨ (¬ p3297) ∨ (¬ p5379) ∨ (¬ p4564) ∨ (¬ p3125) ∨ (¬ p2797))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p2797) ∨ p3755 ∨ (¬ p3297) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    let u6 : (¬ p5379) := (Or.elim h92283 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110949 (p2797 p3297 p3319 p3654 p3755 p4761 p5379 : Prop)
    (h106234 : p4761)
    (h92300 : p3755 ∨ (¬ p3319) ∨ (¬ p3297) ∨ (¬ p5379) ∨ (¬ p4761) ∨ (¬ p2797))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p2797) ∨ p3755 ∨ (¬ p3319) ∨ (¬ p3297) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4761 := h106234;
    let u6 : (¬ p5379) := (Or.elim h92300 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110951 (p2498 p2553 p3246 p3319 p3516 p3654 p5379 : Prop)
    (h109555 : (¬ p3516) ∨ (¬ p5379) ∨ (¬ p3319) ∨ p3246 ∨ p2553 ∨ (¬ p2498))
    (h102542 : p5379 ∨ p3654)
    : p3654 ∨ (¬ p3516) ∨ (¬ p3319) ∨ p3246 ∨ p2553 ∨ (¬ p2498) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5379) := (Or.elim h109555 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102542 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110959 (p3189 p3256 p3848 p5111 : Prop)
    (h19858 : (¬ p3189) ∨ (¬ p3848) ∨ (¬ p5111))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ (¬ p3189) ∨ (¬ p3848) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5111) := (Or.elim h19858 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96299 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110960 (p3005 p3256 p3755 p5111 : Prop)
    (h21750 : (¬ p3005) ∨ p3755 ∨ (¬ p5111))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ (¬ p3005) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5111) := (Or.elim h21750 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96299 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110961 (p3166 p3256 p3286 p5111 : Prop)
    (h95061 : p3286 ∨ (¬ p5111) ∨ (¬ p3166))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ p3286 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5111) := (Or.elim h95061 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96299 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110963 (p3146 p3256 p3266 p3506 p4043 p5111 : Prop)
    (h98691 : p3266 ∨ (¬ p3506) ∨ (¬ p5111) ∨ p3146 ∨ (¬ p4043))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ p3146 ∨ (¬ p4043) ∨ p3266 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5111) := (Or.elim h98691 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110964 (p2727 p3256 p3506 p3707 p3846 p5008 p5111 : Prop)
    (h105469 : p5008)
    (h82323 : p3707 ∨ (¬ p3846) ∨ (¬ p2727) ∨ (¬ p5008) ∨ (¬ p5111) ∨ (¬ p3506))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ (¬ p3846) ∨ (¬ p2727) ∨ p3707 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5008 := h105469;
    let u6 : (¬ p5111) := (Or.elim h82323 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110966 (p2245 p2696 p3005 p3256 p3286 p4733 p5111 : Prop)
    (h105430 : p4733)
    (h93438 : p3286 ∨ (¬ p3005) ∨ (¬ p4733) ∨ (¬ p2245) ∨ (¬ p5111) ∨ (¬ p2696))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ p3286 ∨ (¬ p2696) ∨ (¬ p2245) ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4733 := h105430;
    let u6 : (¬ p5111) := (Or.elim h93438 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110978 (p2417 p2651 p3005 p3201 p3256 p3266 p3506 p3683 p4669 p5111 : Prop)
    (h105415 : p4669)
    (h87923 : p3266 ∨ (¬ p3506) ∨ (¬ p4669) ∨ p2417 ∨ (¬ p3005) ∨ p3201 ∨ p2651 ∨ (¬ p3683) ∨ (¬ p5111))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ (¬ p3005) ∨ p2417 ∨ p3266 ∨ p3201 ∨ p2651 ∨ (¬ p3506) ∨ (¬ p3683) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    let u9 : (¬ p5111) := (Or.elim h87923 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110984 (p2136 p2156 p2860 p3105 p3166 p3256 p3266 p3506 p4033 p4604 p4786 p5111 : Prop)
    (h106293 : p4604)
    (h106425 : p4786)
    (h84584 : p3266 ∨ (¬ p3506) ∨ (¬ p3166) ∨ (¬ p5111) ∨ p3105 ∨ (¬ p2860) ∨ (¬ p4033) ∨ (¬ p4786) ∨ p2156 ∨ (¬ p4604) ∨ (¬ p2136))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ (¬ p3506) ∨ p3105 ∨ (¬ p3166) ∨ (¬ p2860) ∨ p3266 ∨ (¬ p2136) ∨ (¬ p4033) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4604 := h106293;
    let u10 : p4786 := h106425;
    let u11 : (¬ p5111) := (Or.elim h84584 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110989 (p2122 p2246 p2396 p2573 p2744 p3166 p3256 p3266 p3366 p3506 p3905 p4390 p4669 p5111 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h100954 : p3266 ∨ (¬ p5111) ∨ (¬ p3506) ∨ (¬ p3166) ∨ (¬ p2246) ∨ p2122 ∨ p2573 ∨ (¬ p2744) ∨ (¬ p4669) ∨ p2396 ∨ (¬ p3366) ∨ (¬ p4390) ∨ (¬ p3905))
    (h96299 : p5111 ∨ (¬ p3256))
    : (¬ p3256) ∨ p2122 ∨ p3266 ∨ p2573 ∨ p2396 ∨ (¬ p3166) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p2246) ∨ (¬ p3905) ∨ (¬ p4390) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2744 := h106503;
    let u12 : p4669 := h105415;
    let u13 : (¬ p5111) := (Or.elim h100954 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u4 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u9))))))))))))))))))))))))));
    (Or.elim h96299 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110990 (p2641 p3323 p3848 p5274 : Prop)
    (h94417 : p3848 ∨ p2641 ∨ (¬ p5274))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ p3848 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3848) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5274) := (Or.elim h94417 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102539 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110991 (p2797 p3323 p3755 p5274 : Prop)
    (h94955 : (¬ p3755) ∨ p2797 ∨ (¬ p5274))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5274) := (Or.elim h94955 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102539 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110992 (p2331 p3286 p3323 p5274 : Prop)
    (h95305 : (¬ p3286) ∨ p2331 ∨ (¬ p5274))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3286) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5274) := (Or.elim h95305 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102539 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110995 (p2383 p2668 p3266 p3323 p5274 p5284 : Prop)
    (h79234 : (¬ p5274) ∨ (¬ p5284) ∨ (¬ p3266) ∨ p2383 ∨ (¬ p2668))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3266) ∨ p2383 ∨ (¬ p2668) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5274) := (Or.elim h79234 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110999 (p2737 p2797 p3323 p3461 p5274 p5284 : Prop)
    (h93280 : (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p5274) ∨ p2737)
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5274) := (Or.elim h93280 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111000 (p2696 p2797 p3323 p3461 p5274 p5284 : Prop)
    (h93281 : (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p5274) ∨ p2696)
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ p2797 ∨ p2696 ∨ (¬ p3461) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5274) := (Or.elim h93281 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111001 (p3125 p3323 p3461 p4564 p5274 p5284 : Prop)
    (h105401 : p4564)
    (h41141 : (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4564) ∨ (¬ p5274) ∨ (¬ p5284))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    let u5 : (¬ p5274) := (Or.elim h41141 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111009 (p2295 p2608 p3323 p3707 p3830 p5274 p5287 : Prop)
    (h109342 : p5287 ∨ (¬ p3830) ∨ p2608 ∨ (¬ p3707) ∨ (¬ p5274) ∨ (¬ p2295))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ p5287 ∨ (¬ p3830) ∨ p2608 ∨ (¬ p3707) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5287) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5274) := (Or.elim h109342 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111012 (p2312 p2668 p3323 p3767 p4405 p5274 p5284 p5300 : Prop)
    (h105512 : p4405)
    (h52575 : (¬ p2312) ∨ (¬ p2668) ∨ (¬ p3767) ∨ (¬ p4405) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5300))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p5300) ∨ (¬ p3767) ∨ (¬ p2312) ∨ (¬ p2668) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p5300 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p5274) := (Or.elim h52575 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111016 (p2427 p2819 p3323 p3631 p3707 p4337 p4909 p5274 p5284 : Prop)
    (h110619 : (¬ p3631) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p2427) ∨ (¬ p4909) ∨ (¬ p2819))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3631) ∨ (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p2427) ∨ (¬ p4909) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5274) := (Or.elim h110619 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111017 (p2254 p2331 p2518 p2528 p3323 p3379 p3461 p4604 p5274 p5284 : Prop)
    (h105366 : p2254)
    (h106293 : p4604)
    (h81483 : (¬ p5284) ∨ (¬ p2518) ∨ (¬ p5274) ∨ (¬ p2254) ∨ (¬ p3461) ∨ (¬ p2528) ∨ (¬ p3379) ∨ p2331 ∨ (¬ p4604))
    (h102539 : p5274 ∨ p3323)
    : p3323 ∨ (¬ p3461) ∨ (¬ p2518) ∨ p2331 ∨ (¬ p2528) ∨ (¬ p5284) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4604 := h106293;
    let u9 : (¬ p5274) := (Or.elim h81483 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h102539 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111022 (p3527 p3941 p4181 p5307 : Prop)
    (h34673 : (¬ p3941) ∨ p4181 ∨ (¬ p5307))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ p4181 ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4181) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5307) := (Or.elim h34673 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96266 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111023 (p2459 p3073 p3527 p5307 : Prop)
    (h37012 : (¬ p2459) ∨ p3073 ∨ (¬ p5307))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ p3073 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5307) := (Or.elim h37012 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96266 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111026 (p2881 p3399 p3449 p3527 p4914 p5307 : Prop)
    (h93370 : (¬ p5307) ∨ p3399 ∨ p2881 ∨ (¬ p3449) ∨ (¬ p4914))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p2881 ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h93370 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111027 (p2264 p3040 p3399 p3449 p3527 p5307 : Prop)
    (h93373 : (¬ p5307) ∨ p3399 ∨ (¬ p3449) ∨ p2264 ∨ (¬ p3040))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p2264 ∨ (¬ p3040) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h93373 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111028 (p3399 p3449 p3527 p4442 p5307 p5559 : Prop)
    (h106189 : p5559)
    (h93375 : (¬ p4442) ∨ p3399 ∨ (¬ p3449) ∨ (¬ p5307) ∨ (¬ p5559))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p4442) ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5559 := h106189;
    let u5 : (¬ p5307) := (Or.elim h93375 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111029 (p2807 p2911 p3166 p3527 p5074 p5307 : Prop)
    (h107356 : (¬ p5307) ∨ (¬ p3166) ∨ p2911 ∨ p2807 ∨ (¬ p5074))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p5074) ∨ p2911 ∨ p2807 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h107356 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111030 (p3399 p3449 p3527 p3631 p4666 p5307 : Prop)
    (h105658 : p4666)
    (h101978 : p3399 ∨ (¬ p3449) ∨ (¬ p4666) ∨ (¬ p5307) ∨ p3631)
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    let u5 : (¬ p5307) := (Or.elim h101978 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111032 (p2707 p2717 p3399 p3449 p3527 p5307 : Prop)
    (h108320 : (¬ p2707) ∨ (¬ p3449) ∨ p3399 ∨ (¬ p5307) ∨ p2717)
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p2707) ∨ (¬ p3449) ∨ p3399 ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h108320 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111033 (p2177 p3309 p3399 p3449 p3527 p5307 : Prop)
    (h108656 : (¬ p3309) ∨ (¬ p5307) ∨ p2177 ∨ p3399 ∨ (¬ p3449))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p3309) ∨ p2177 ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h108656 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111034 (p2911 p2922 p3399 p3449 p3527 p5307 : Prop)
    (h108923 : (¬ p2922) ∨ (¬ p5307) ∨ p3399 ∨ (¬ p3449) ∨ p2911)
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p2922) ∨ p3399 ∨ (¬ p3449) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5307) := (Or.elim h108923 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111036 (p2177 p2437 p3083 p3527 p4370 p4712 p5307 : Prop)
    (h105422 : p4712)
    (h75136 : (¬ p5307) ∨ (¬ p4370) ∨ p2437 ∨ (¬ p4712) ∨ (¬ p3083) ∨ p2177)
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p4370) ∨ (¬ p3083) ∨ p2437 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    let u6 : (¬ p5307) := (Or.elim h75136 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111037 (p2177 p2470 p3389 p3527 p4370 p4712 p5307 : Prop)
    (h105422 : p4712)
    (h77503 : (¬ p5307) ∨ (¬ p2470) ∨ p3389 ∨ (¬ p4370) ∨ p2177 ∨ (¬ p4712))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p4370) ∨ p3389 ∨ (¬ p2470) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    let u6 : (¬ p5307) := (Or.elim h77503 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111038 (p2470 p2881 p3389 p3527 p4370 p4647 p5307 : Prop)
    (h105412 : p4647)
    (h77523 : (¬ p5307) ∨ (¬ p2470) ∨ (¬ p4647) ∨ p3389 ∨ (¬ p4370) ∨ p2881)
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p4370) ∨ p2881 ∨ (¬ p2470) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4647 := h105412;
    let u6 : (¬ p5307) := (Or.elim h77523 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111041 (p3032 p3399 p3449 p3527 p4391 p5307 p5559 : Prop)
    (h106189 : p5559)
    (h97768 : p3399 ∨ (¬ p3032) ∨ (¬ p5559) ∨ (¬ p4391) ∨ (¬ p5307) ∨ (¬ p3449))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p4391) ∨ (¬ p3032) ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5559 := h106189;
    let u6 : (¬ p5307) := (Or.elim h97768 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111042 (p3093 p3319 p3449 p3527 p3990 p4503 p5307 : Prop)
    (h106530 : p4503)
    (h102175 : p3093 ∨ (¬ p3449) ∨ p3319 ∨ (¬ p5307) ∨ (¬ p3990) ∨ (¬ p4503))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p3449) ∨ p3093 ∨ p3319 ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4503 := h106530;
    let u6 : (¬ p5307) := (Or.elim h102175 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111048 (p2187 p2284 p2341 p2819 p2946 p3073 p3527 p3609 p5206 p5307 : Prop)
    (h108329 : (¬ p2819) ∨ (¬ p2187) ∨ p2341 ∨ (¬ p2284) ∨ (¬ p2946) ∨ p3073 ∨ (¬ p3609) ∨ (¬ p5206) ∨ (¬ p5307))
    (h96266 : p5307 ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p2819) ∨ (¬ p2187) ∨ p2341 ∨ (¬ p2284) ∨ (¬ p2946) ∨ p3073 ∨ (¬ p3609) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5307) := (Or.elim h108329 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => r7))))))))))))))));
    (Or.elim h96266 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111052 (p3051 p3246 p4032 p4402 : Prop)
    (h82985 : p4032 ∨ p3051 ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p4032 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4032) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4402) := (Or.elim h82985 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h100360 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111053 (p2901 p3115 p3246 p4402 : Prop)
    (h82986 : (¬ p3115) ∨ p2901 ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p2901 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4402) := (Or.elim h82986 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h100360 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111054 (p2870 p3105 p3246 p4402 : Prop)
    (h82994 : (¬ p3105) ∨ p2870 ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p2870 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4402) := (Or.elim h82994 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h100360 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111056 (p2891 p2972 p3246 p4402 : Prop)
    (h92707 : (¬ p4402) ∨ (¬ p2972) ∨ p2891)
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p2891 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4402) := (Or.elim h92707 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h100360 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111057 (p2761 p3246 p3516 p4322 p4402 : Prop)
    (h68259 : (¬ p2761) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p3516))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p3516) ∨ (¬ p2761) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4402) := (Or.elim h68259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111058 (p2143 p3051 p3105 p3246 p4402 : Prop)
    (h82990 : (¬ p3105) ∨ p3051 ∨ (¬ p2143) ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p3105) ∨ p3051 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4402) := (Or.elim h82990 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h100360 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111059 (p2230 p2427 p2761 p3246 p4322 p4402 : Prop)
    (h75836 : (¬ p4322) ∨ (¬ p2761) ∨ (¬ p4402) ∨ p2427 ∨ p2230)
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p4322) ∨ p2427 ∨ p2230 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4402) := (Or.elim h75836 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111063 (p2761 p2881 p3246 p3434 p4322 p4402 : Prop)
    (h63918 : (¬ p2761) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p4322) ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p2761) ∨ (¬ p4322) ∨ (¬ p2881) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4402) := (Or.elim h63918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111065 (p2396 p3246 p3631 p3707 p4322 p4402 : Prop)
    (h110532 : p3631 ∨ (¬ p3707) ∨ (¬ p2396) ∨ (¬ p4322) ∨ (¬ p4402))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p3631 ∨ (¬ p3707) ∨ (¬ p2396) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4402) := (Or.elim h110532 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111067 (p2427 p3246 p3767 p4207 p4322 p4402 p4539 : Prop)
    (h105395 : p4539)
    (h82993 : (¬ p3767) ∨ (¬ p4322) ∨ p2427 ∨ (¬ p4207) ∨ (¬ p4402) ∨ (¬ p4539))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p3767) ∨ (¬ p4322) ∨ p2427 ∨ (¬ p4207) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4539 := h105395;
    let u6 : (¬ p4402) := (Or.elim h82993 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111068 (p3246 p3461 p3564 p4204 p4322 p4402 p4718 : Prop)
    (h105425 : p4718)
    (h51681 : (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4204) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4718))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p3564) ∨ (¬ p3461) ∨ (¬ p4322) ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4718 := h105425;
    let u6 : (¬ p4402) := (Or.elim h51681 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111070 (p2177 p2619 p3105 p3246 p4132 p4402 p4556 : Prop)
    (h105399 : p4556)
    (h84774 : (¬ p4402) ∨ (¬ p3105) ∨ (¬ p4556) ∨ p2619 ∨ (¬ p4132) ∨ (¬ p2177))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ (¬ p4132) ∨ p2619 ∨ (¬ p2177) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    let u6 : (¬ p4402) := (Or.elim h84774 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111071 (p3246 p3516 p3631 p3767 p4322 p4402 p4914 : Prop)
    (h110107 : p3516 ∨ (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914))
    (h100360 : p4402 ∨ p3246)
    : p3246 ∨ p3516 ∨ (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4402) := (Or.elim h110107 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100360 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111087 (p3166 p3256 p3286 p4349 : Prop)
    (h93212 : (¬ p4349) ∨ (¬ p3286) ∨ p3166)
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ p3166 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4349) := (Or.elim h93212 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102494 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111089 (p3005 p3256 p3755 p4349 : Prop)
    (h94943 : (¬ p3755) ∨ (¬ p4349) ∨ p3005)
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ p3005 ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4349) := (Or.elim h94943 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102494 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111090 (p3189 p3256 p3852 p4349 : Prop)
    (h110653 : (¬ p3852) ∨ (¬ p4349) ∨ p3189)
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p3852) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3852 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4349) := (Or.elim h110653 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102494 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111091 (p2331 p3256 p3286 p4196 p4349 : Prop)
    (h89467 : (¬ p3286) ∨ (¬ p4349) ∨ p2331 ∨ (¬ p4196))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p4196) ∨ (¬ p3286) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4349) := (Or.elim h89467 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111094 (p2331 p3166 p3256 p4349 p4421 : Prop)
    (h94563 : (¬ p4349) ∨ p3166 ∨ (¬ p4421) ∨ (¬ p2331))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ p3166 ∨ (¬ p2331) ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4349) := (Or.elim h94563 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111095 (p3146 p3256 p3266 p4349 p5063 p5284 : Prop)
    (h105474 : p5063)
    (h50141 : (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4349) ∨ (¬ p5063) ∨ (¬ p5284))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5063 := h105474;
    let u5 : (¬ p4349) := (Or.elim h50141 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111102 (p2911 p2996 p3256 p3842 p4349 p4378 p4653 : Prop)
    (h94371 : (¬ p3842) ∨ (¬ p2996) ∨ (¬ p4653) ∨ p2911 ∨ (¬ p4378) ∨ (¬ p4349))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p4378) ∨ (¬ p2996) ∨ (¬ p3842) ∨ p2911 ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4349) := (Or.elim h94371 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111103 (p3256 p3309 p3319 p3707 p4349 p4417 p5284 : Prop)
    (h109542 : (¬ p3319) ∨ (¬ p4417) ∨ p3309 ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p5284))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p3319) ∨ (¬ p4417) ∨ p3309 ∨ (¬ p3707) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4349) := (Or.elim h109542 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111104 (p2553 p3256 p3276 p4349 p4405 p4417 p4422 p5284 : Prop)
    (h105512 : p4405)
    (h93292 : (¬ p5284) ∨ (¬ p4349) ∨ (¬ p4422) ∨ (¬ p3276) ∨ (¬ p4405) ∨ p2553 ∨ (¬ p4417))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p4422) ∨ (¬ p5284) ∨ (¬ p3276) ∨ (¬ p4417) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p4349) := (Or.elim h93292 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111107 (p2427 p3256 p3661 p3691 p3767 p4349 p4702 p5284 p5300 : Prop)
    (h106079 : p4702)
    (h54207 : (¬ p2427) ∨ (¬ p3661) ∨ (¬ p3691) ∨ (¬ p3767) ∨ (¬ p4349) ∨ (¬ p4702) ∨ (¬ p5284) ∨ (¬ p5300))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p3767) ∨ (¬ p3691) ∨ (¬ p5284) ∨ (¬ p2427) ∨ (¬ p3661) ∨ (¬ p5300) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5300 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4702 := h106079;
    let u8 : (¬ p4349) := (Or.elim h54207 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111116 (p2220 p2254 p2493 p2950 p3256 p3266 p3379 p3564 p4311 p4330 p4349 p5284 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h94753 : (¬ p5284) ∨ (¬ p3266) ∨ p2220 ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4311) ∨ (¬ p2493) ∨ (¬ p4349) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2950))
    (h102494 : p4349 ∨ p3256)
    : p3256 ∨ (¬ p3564) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p2493) ∨ p2220 ∨ (¬ p5284) ∨ (¬ p2950) ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    let u10 : p4330 := h106329;
    let u11 : (¬ p4349) := (Or.elim h94753 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u7))))))))))))))))))))));
    (Or.elim h102494 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111121 (p2528 p3609 p3641 p5373 : Prop)
    (h76783 : (¬ p5373) ∨ p3609 ∨ (¬ p2528))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p2528) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5373) := (Or.elim h76783 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96246 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111122 (p3641 p4404 p4804 p5373 : Prop)
    (h37608 : (¬ p4404) ∨ p4804 ∨ (¬ p5373))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ p4804 ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4804) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5373) := (Or.elim h37608 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96246 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111124 (p2470 p3367 p3537 p3641 p5373 : Prop)
    (h76790 : (¬ p3537) ∨ (¬ p5373) ∨ p3367 ∨ p2470)
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3537) ∨ p2470 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5373) := (Or.elim h76790 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111125 (p2088 p2475 p3609 p3641 p5373 : Prop)
    (h89922 : p3609 ∨ (¬ p5373) ∨ (¬ p2475) ∨ (¬ p2088))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ p3609 ∨ (¬ p2475) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5373) := (Or.elim h89922 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111127 (p2850 p3367 p3537 p3641 p4610 p5373 : Prop)
    (h76779 : (¬ p3537) ∨ (¬ p5373) ∨ p3367 ∨ p2850 ∨ (¬ p4610))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3537) ∨ (¬ p4610) ∨ p3367 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5373) := (Or.elim h76779 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111128 (p2098 p2509 p2598 p3641 p5214 p5373 : Prop)
    (h105492 : p5214)
    (h76788 : (¬ p5373) ∨ (¬ p2098) ∨ (¬ p5214) ∨ p2598 ∨ (¬ p2509))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p2098) ∨ (¬ p2509) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5214 := h105492;
    let u5 : (¬ p5373) := (Or.elim h76788 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111132 (p2528 p2598 p3367 p3537 p3589 p3641 p5373 : Prop)
    (h81797 : (¬ p3537) ∨ (¬ p5373) ∨ p3367 ∨ (¬ p3589) ∨ (¬ p2598) ∨ (¬ p2528))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3537) ∨ (¬ p2528) ∨ p3367 ∨ (¬ p2598) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5373) := (Or.elim h81797 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111134 (p2098 p2437 p2440 p2598 p3641 p4186 p5373 : Prop)
    (h93146 : (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 ∨ (¬ p5373) ∨ (¬ p4186))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5373) := (Or.elim h93146 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111139 (p2187 p2192 p2210 p2459 p2470 p3609 p3641 p4133 p5193 p5373 : Prop)
    (h105488 : p5193)
    (h105712 : p4133)
    (h76773 : (¬ p5373) ∨ p3609 ∨ (¬ p2459) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p2187) ∨ (¬ p5193) ∨ (¬ p4133) ∨ p2470)
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ p2470 ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p4133 := h105712;
    let u9 : (¬ p5373) := (Or.elim h76773 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u1 r7))))))))))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111143 (p2139 p2156 p2274 p2470 p3266 p3609 p3641 p3791 p3905 p4826 p5373 : Prop)
    (h105444 : p4826)
    (h88012 : (¬ p3791) ∨ p3266 ∨ (¬ p3905) ∨ p2470 ∨ p3609 ∨ (¬ p2156) ∨ (¬ p5373) ∨ (¬ p2139) ∨ (¬ p2274) ∨ (¬ p4826))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3791) ∨ p3266 ∨ p2470 ∨ p3609 ∨ (¬ p3905) ∨ (¬ p2274) ∨ (¬ p2156) ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4826 := h105444;
    let u10 : (¬ p5373) := (Or.elim h88012 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111144 (p2098 p2528 p2598 p2748 p2761 p2972 p3115 p3368 p3641 p5284 p5373 : Prop)
    (h110869 : (¬ p3115) ∨ (¬ p5284) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p2098) ∨ p2972 ∨ p2598 ∨ (¬ p2748) ∨ (¬ p3368) ∨ (¬ p5373))
    (h96246 : p5373 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3115) ∨ (¬ p5284) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p2098) ∨ p2972 ∨ p2598 ∨ (¬ p2748) ∨ (¬ p3368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5373) := (Or.elim h110869 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => r8))))))))))))))))));
    (Or.elim h96246 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111153 (p2839 p2850 p3054 p3367 : Prop)
    (h81223 : (¬ p2839) ∨ p3367 ∨ (¬ p3054))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p2839) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3054) := (Or.elim h81223 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102320 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111154 (p2132 p2598 p2850 p3054 : Prop)
    (h90719 : (¬ p3054) ∨ (¬ p2132) ∨ p2598)
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p2132) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3054) := (Or.elim h90719 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102320 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111155 (p2406 p2850 p3054 p3590 p3698 : Prop)
    (h29207 : (¬ p2406) ∨ (¬ p3054) ∨ (¬ p3590) ∨ (¬ p3698))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p2406) ∨ (¬ p3698) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3054) := (Or.elim h29207 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111156 (p2230 p2850 p3054 p3717 p6116 : Prop)
    (h110777 : p6116 ∨ p3717 ∨ (¬ p2230) ∨ (¬ p3054))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p6116 ∨ p3717 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6116) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3054) := (Or.elim h110777 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h102320 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111158 (p2192 p2563 p2850 p2870 p2891 p3054 : Prop)
    (h79966 : p2870 ∨ (¬ p3054) ∨ (¬ p2891) ∨ p2192 ∨ (¬ p2563))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2192 ∨ p2870 ∨ (¬ p2891) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3054) := (Or.elim h79966 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111159 (p2230 p2563 p2850 p2860 p3054 p4730 : Prop)
    (h106074 : p4730)
    (h83201 : (¬ p2563) ∨ (¬ p2230) ∨ (¬ p3054) ∨ (¬ p4730) ∨ p2860)
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2860 ∨ (¬ p2230) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p3054) := (Or.elim h83201 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111160 (p2230 p2850 p2982 p3054 p3105 p4730 : Prop)
    (h106074 : p4730)
    (h84515 : (¬ p3054) ∨ p3105 ∨ (¬ p4730) ∨ (¬ p2230) ∨ (¬ p2982))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p3105 ∨ (¬ p2982) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p3054) := (Or.elim h84515 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111161 (p2850 p2982 p3054 p3105 p3422 p4717 : Prop)
    (h105424 : p4717)
    (h84551 : p3105 ∨ (¬ p2982) ∨ (¬ p4717) ∨ (¬ p3054) ∨ (¬ p3422))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p3105 ∨ (¬ p2982) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p3054) := (Or.elim h84551 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111162 (p2274 p2373 p2563 p2619 p2850 p3054 : Prop)
    (h84694 : (¬ p3054) ∨ p2563 ∨ p2274 ∨ (¬ p2373) ∨ p2619)
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2563 ∨ (¬ p2373) ∨ p2619 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3054) := (Or.elim h84694 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111163 (p2230 p2373 p2619 p2850 p3054 p4730 : Prop)
    (h106074 : p4730)
    (h84764 : (¬ p3054) ∨ p2619 ∨ (¬ p4730) ∨ (¬ p2230) ∨ (¬ p2373))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2619 ∨ (¬ p2373) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p3054) := (Or.elim h84764 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111165 (p2427 p2850 p2870 p3054 p3422 p4717 : Prop)
    (h105424 : p4717)
    (h86817 : p2870 ∨ (¬ p3422) ∨ (¬ p4717) ∨ (¬ p3054) ∨ (¬ p2427))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2870 ∨ (¬ p3422) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p3054) := (Or.elim h86817 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111166 (p2509 p2850 p2870 p2901 p3054 p3402 p3641 : Prop)
    (h77403 : (¬ p2901) ∨ (¬ p3641) ∨ p2870 ∨ (¬ p3402) ∨ (¬ p2509) ∨ (¬ p3054))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p2509) ∨ p2870 ∨ (¬ p2901) ∨ (¬ p3641) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3054) := (Or.elim h77403 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111167 (p2192 p2230 p2563 p2850 p3054 p4243 p4730 : Prop)
    (h106074 : p4730)
    (h79918 : p2192 ∨ (¬ p4243) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p4730) ∨ (¬ p2230))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ p2192 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4730 := h106074;
    let u6 : (¬ p3054) := (Or.elim h79918 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111170 (p2156 p2440 p2850 p2860 p3054 p4109 p4750 : Prop)
    (h105433 : p4750)
    (h92424 : p2860 ∨ p2440 ∨ (¬ p2156) ∨ (¬ p4750) ∨ (¬ p4109) ∨ (¬ p3054))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p2156) ∨ p2860 ∨ p2440 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : (¬ p3054) := (Or.elim h92424 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111181 (p2254 p2396 p2563 p2651 p2850 p2860 p3054 p3399 p3683 p4075 p4260 : Prop)
    (h105366 : p2254)
    (h83356 : (¬ p4260) ∨ (¬ p4075) ∨ p2651 ∨ (¬ p3054) ∨ (¬ p3683) ∨ p2860 ∨ (¬ p3399) ∨ (¬ p2563) ∨ (¬ p2396) ∨ (¬ p2254))
    (h102320 : p3054 ∨ p2850)
    : p2850 ∨ (¬ p4075) ∨ (¬ p4260) ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p2563) ∨ p2651 ∨ (¬ p3683) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    let u10 : (¬ p3054) := (Or.elim h83356 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h102320 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111187 (p2166 p2210 p3449 p4496 : Prop)
    (h80538 : p3449 ∨ (¬ p2210) ∨ (¬ p4496))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3449 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4496) := (Or.elim h80538 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102268 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111188 (p2166 p4377 p4496 p5312 : Prop)
    (h106170 : p4377)
    (h38829 : (¬ p4377) ∨ (¬ p4496) ∨ p5312)
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p5312 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5312) := (fun h => hn (Or.inr h));
    let u2 : p4377 := h106170;
    let u3 : (¬ p4496) := (Or.elim h38829 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102268 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111194 (p2166 p2210 p3073 p3830 p4496 : Prop)
    (h110471 : (¬ p3073) ∨ (¬ p4496) ∨ p3830 ∨ (¬ p2210))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3073) ∨ p3830 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4496) := (Or.elim h110471 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111195 (p2166 p2373 p3073 p3146 p4496 p4632 : Prop)
    (h106257 : p4632)
    (h78970 : p3146 ∨ (¬ p3073) ∨ (¬ p4632) ∨ p2373 ∨ (¬ p4496))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2373 ∨ p3146 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    let u5 : (¬ p4496) := (Or.elim h78970 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111196 (p2166 p2192 p3073 p3146 p4496 p4509 : Prop)
    (h105392 : p4509)
    (h80010 : p3146 ∨ p2192 ∨ (¬ p4496) ∨ (¬ p3073) ∨ (¬ p4509))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3146 ∨ (¬ p3073) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    let u5 : (¬ p4496) := (Or.elim h80010 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111197 (p2166 p3073 p3146 p3156 p4496 p4960 : Prop)
    (h106209 : p4960)
    (h80173 : p3146 ∨ (¬ p3073) ∨ (¬ p4960) ∨ (¬ p4496) ∨ p3156)
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3146 ∨ p3156 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    let u5 : (¬ p4496) := (Or.elim h80173 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111204 (p2166 p2901 p3073 p3146 p4119 p4496 p4960 : Prop)
    (h106209 : p4960)
    (h80134 : p3146 ∨ p2901 ∨ (¬ p3073) ∨ (¬ p4960) ∨ (¬ p4119) ∨ (¬ p4496))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3146 ∨ (¬ p3073) ∨ (¬ p4119) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4960 := h106209;
    let u6 : (¬ p4496) := (Or.elim h80134 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111205 (p2166 p2427 p3073 p3146 p4034 p4496 p4904 : Prop)
    (h80156 : p3146 ∨ (¬ p3073) ∨ (¬ p4904) ∨ (¬ p4034) ∨ p2427 ∨ (¬ p4496))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2427 ∨ p3146 ∨ (¬ p4034) ∨ (¬ p3073) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4496) := (Or.elim h80156 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => r4))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111211 (p2166 p2891 p3073 p3609 p4078 p4185 p4496 p4555 : Prop)
    (h105542 : p4555)
    (h91611 : (¬ p4496) ∨ (¬ p4185) ∨ (¬ p4555) ∨ p2891 ∨ (¬ p3073) ∨ p3609 ∨ (¬ p4078))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3073) ∨ (¬ p4078) ∨ (¬ p4185) ∨ p3609 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4555 := h105542;
    let u7 : (¬ p4496) := (Or.elim h91611 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111212 (p2088 p2166 p2192 p3073 p3961 p4283 p4496 p4558 : Prop)
    (h105400 : p4558)
    (h93558 : (¬ p3073) ∨ (¬ p4558) ∨ p2192 ∨ (¬ p4496) ∨ (¬ p4283) ∨ p2088 ∨ (¬ p3961))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p4283) ∨ (¬ p3073) ∨ p2088 ∨ p2192 ∨ (¬ p3961) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4558 := h105400;
    let u7 : (¬ p4496) := (Or.elim h93558 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111215 (p2166 p2210 p2598 p2911 p3073 p3146 p3201 p4496 p4736 p4902 : Prop)
    (h105431 : p4736)
    (h105456 : p4902)
    (h80230 : (¬ p3073) ∨ p3201 ∨ p2598 ∨ p2911 ∨ (¬ p4902) ∨ (¬ p4736) ∨ (¬ p2210) ∨ (¬ p4496) ∨ p3146)
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2911 ∨ p2598 ∨ p3146 ∨ p3201 ∨ (¬ p3073) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4902 := h105456;
    let u9 : (¬ p4496) := (Or.elim h80230 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111216 (p2132 p2166 p2331 p2668 p2737 p3073 p3146 p3361 p4418 p4433 p4496 : Prop)
    (h106150 : p4433)
    (h80229 : p2331 ∨ (¬ p3073) ∨ (¬ p3361) ∨ (¬ p2132) ∨ p2737 ∨ (¬ p4496) ∨ (¬ p4418) ∨ p3146 ∨ p2668 ∨ (¬ p4433))
    (h102268 : p4496 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2668 ∨ (¬ p3073) ∨ p3146 ∨ (¬ p4418) ∨ (¬ p2132) ∨ (¬ p3361) ∨ p2737 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4433 := h106150;
    let u10 : (¬ p4496) := (Or.elim h80229 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h102268 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111221 (p2982 p4697 p4947 p5059 : Prop)
    (h27229 : p4697 ∨ (¬ p4947) ∨ (¬ p5059))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ p4697 ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4697) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4947) := (Or.elim h27229 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96342 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111224 (p2230 p2440 p2982 p3343 p4322 p4947 : Prop)
    (h74543 : (¬ p4322) ∨ p3343 ∨ p2440 ∨ p2230 ∨ (¬ p4947))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ p3343 ∨ (¬ p4322) ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4947) := (Or.elim h74543 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111226 (p2440 p2563 p2982 p3343 p4947 p5043 : Prop)
    (h105471 : p5043)
    (h89551 : (¬ p4947) ∨ (¬ p5043) ∨ (¬ p2563) ∨ p2440 ∨ p3343)
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ p3343 ∨ p2440 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5043 := h105471;
    let u5 : (¬ p4947) := (Or.elim h89551 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111230 (p2230 p2982 p3115 p3346 p4705 p4947 : Prop)
    (h106238 : p4705)
    (h41921 : (¬ p2230) ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p4705) ∨ (¬ p4947))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    let u5 : (¬ p4947) := (Or.elim h41921 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111232 (p2396 p2761 p2982 p3276 p4260 p4947 : Prop)
    (h108964 : p2761 ∨ (¬ p4260) ∨ (¬ p3276) ∨ (¬ p2396) ∨ (¬ p4947))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ p2761 ∨ (¬ p4260) ∨ (¬ p3276) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4947) := (Or.elim h108964 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111236 (p2363 p2982 p3115 p3156 p4134 p4695 p4947 : Prop)
    (h105379 : p4134)
    (h95992 : p2363 ∨ (¬ p4695) ∨ p3156 ∨ (¬ p4947) ∨ (¬ p4134) ∨ (¬ p3115))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ p2363 ∨ (¬ p4695) ∨ (¬ p3115) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4134 := h105379;
    let u6 : (¬ p4947) := (Or.elim h95992 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111247 (p2230 p2254 p2440 p2608 p2655 p2982 p3343 p3537 p3609 p4947 p5059 : Prop)
    (h105366 : p2254)
    (h75042 : (¬ p3537) ∨ (¬ p2608) ∨ (¬ p2254) ∨ p2440 ∨ (¬ p2655) ∨ p2230 ∨ (¬ p3609) ∨ (¬ p4947) ∨ p3343 ∨ (¬ p5059))
    (h96342 : p4947 ∨ p2982)
    : p2982 ∨ (¬ p3609) ∨ (¬ p3537) ∨ p2440 ∨ (¬ p2608) ∨ p2230 ∨ p3343 ∨ (¬ p2655) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    let u10 : (¬ p4947) := (Or.elim h75042 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h96342 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111255 (p3276 p3343 p5175 p5284 : Prop)
    (h107915 : (¬ p3276) ∨ (¬ p5284) ∨ (¬ p5175))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3276) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5175) := (Or.elim h107915 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102651 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111256 (p3193 p3343 p3487 p5175 p5176 : Prop)
    (h16652 : (¬ p3193) ∨ (¬ p3487) ∨ (¬ p5175) ∨ (¬ p5176))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p5176) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5176 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5175) := (Or.elim h16652 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111257 (p2440 p2727 p3343 p3842 p4953 p5175 : Prop)
    (h94393 : p2727 ∨ (¬ p5175) ∨ (¬ p3842) ∨ (¬ p2440) ∨ (¬ p4953))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3842) ∨ p2727 ∨ (¬ p4953) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5175) := (Or.elim h94393 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111260 (p2493 p3136 p3193 p3343 p3755 p5175 : Prop)
    (h95023 : (¬ p3755) ∨ (¬ p3193) ∨ (¬ p5175) ∨ p3136 ∨ (¬ p2493))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3755) ∨ (¬ p3193) ∨ p3136 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5175) := (Or.elim h95023 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111262 (p3146 p3343 p3641 p4158 p5107 p5160 p5175 : Prop)
    (h106187 : p4158)
    (h55160 : (¬ p3146) ∨ (¬ p3641) ∨ (¬ p4158) ∨ (¬ p5107) ∨ (¬ p5160) ∨ (¬ p5175))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p5107) ∨ (¬ p5160) ∨ (¬ p3641) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4158 := h106187;
    let u6 : (¬ p5175) := (Or.elim h55160 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111270 (p2331 p2651 p3276 p3343 p3461 p4421 p5175 : Prop)
    (h98157 : (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p5175) ∨ (¬ p4421) ∨ (¬ p2331))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p4421) ∨ (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5175) := (Or.elim h98157 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111272 (p2406 p3193 p3343 p3707 p4953 p5175 p5284 : Prop)
    (h109389 : p3193 ∨ (¬ p3707) ∨ (¬ p5284) ∨ (¬ p5175) ∨ (¬ p4953) ∨ p2406)
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ p3193 ∨ (¬ p3707) ∨ (¬ p5284) ∨ (¬ p4953) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5175) := (Or.elim h109389 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111273 (p2563 p2630 p2651 p2982 p3286 p3343 p5175 : Prop)
    (h109970 : p2982 ∨ (¬ p3286) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2563) ∨ (¬ p5175))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ p2982 ∨ (¬ p3286) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5175) := (Or.elim h109970 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111286 (p2651 p2727 p2996 p3266 p3286 p3343 p3461 p3631 p4450 p4623 p4952 p5175 : Prop)
    (h107836 : p2996 ∨ (¬ p4623) ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p5175) ∨ (¬ p4952) ∨ (¬ p4450))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ p2996 ∨ (¬ p4623) ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p4952) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p5175) := (Or.elim h107836 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111287 (p2156 p2246 p2274 p2396 p2630 p2651 p2749 p3343 p3645 p3755 p4638 p4877 p5175 : Prop)
    (h105451 : p4877)
    (h105409 : p4638)
    (h94993 : (¬ p5175) ∨ (¬ p2246) ∨ p2630 ∨ (¬ p2749) ∨ (¬ p4877) ∨ p2396 ∨ (¬ p2651) ∨ (¬ p3645) ∨ (¬ p3755) ∨ p2156 ∨ p2274 ∨ (¬ p4638))
    (h102651 : p5175 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3755) ∨ (¬ p3645) ∨ p2156 ∨ p2630 ∨ p2396 ∨ p2274 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4877 := h105451;
    let u11 : p4638 := h105409;
    let u12 : (¬ p5175) := (Or.elim h94993 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u6 q10))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h102651 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111289 (p3193 p3343 p3487 p5176 : Prop)
    (h111256 : (¬ p3343) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p5176))
    (h102376 : p5176 ∨ (¬ p3343))
    : (¬ p3343) ∨ (¬ p3193) ∨ (¬ p3487) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5176) := (Or.elim h111256 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102376 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111292 (p4053 p4435 p6164 : Prop)
    (h14706 : p4053 ∨ p6164)
    (h108107 : p4435 ∨ (¬ p6164))
    : p4435 ∨ p4053 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4053) := (fun h => hn (Or.inr h));
    let u2 : p6164 := (Or.elim h14706 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h108107 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step111297 (p2274 p3093 p4053 p4393 p4435 : Prop)
    (h43431 : (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4393))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p4393) ∨ (¬ p3093) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4053) := (Or.elim h43431 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step111299 (p2797 p4053 p4228 p4435 p4759 : Prop)
    (h110221 : p4228 ∨ (¬ p4053) ∨ (¬ p4759) ∨ p2797)
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ p4228 ∨ (¬ p4759) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4053) := (Or.elim h110221 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step111300 (p2860 p4053 p4338 p4393 p4435 p4878 : Prop)
    (h105452 : p4878)
    (h96127 : (¬ p4393) ∨ (¬ p4053) ∨ (¬ p4338) ∨ p2860 ∨ (¬ p4878))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p4393) ∨ p2860 ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    let u5 : (¬ p4053) := (Or.elim h96127 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step111302 (p2619 p3093 p4053 p4193 p4329 p4435 : Prop)
    (h46922 : (¬ p2619) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4193) ∨ (¬ p4329))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p4329) ∨ (¬ p4193) ∨ (¬ p3093) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4053) := (Or.elim h46922 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step111303 (p3093 p3399 p4053 p4427 p4435 p5477 : Prop)
    (h100636 : (¬ p4053) ∨ p3399 ∨ (¬ p4427) ∨ (¬ p3093) ∨ (¬ p5477))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p5477) ∨ p3399 ∨ (¬ p4427) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4053) := (Or.elim h100636 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step111306 (p2406 p2505 p4053 p4435 p4717 p5514 : Prop)
    (h105424 : p4717)
    (h102502 : (¬ p4053) ∨ (¬ p5514) ∨ p2406 ∨ (¬ p2505) ∨ (¬ p4717))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p5514) ∨ (¬ p2505) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p4053) := (Or.elim h102502 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step111308 (p2363 p3073 p3325 p4053 p4371 p4435 p5477 : Prop)
    (h96548 : (¬ p4053) ∨ p3073 ∨ (¬ p4371) ∨ (¬ p5477) ∨ (¬ p3325) ∨ (¬ p2363))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p5477) ∨ (¬ p3325) ∨ (¬ p2363) ∨ p3073 ∨ (¬ p4371) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4053) := (Or.elim h96548 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step111312 (p2440 p3019 p3918 p4053 p4337 p4435 p4717 p5514 : Prop)
    (h105424 : p4717)
    (h61181 : (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3918) ∨ (¬ p4053) ∨ (¬ p4337) ∨ (¬ p4717) ∨ (¬ p5514))
    (h111292 : p4435 ∨ p4053)
    : p4435 ∨ (¬ p5514) ∨ (¬ p3019) ∨ (¬ p4337) ∨ (¬ p3918) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    let u7 : (¬ p4053) := (Or.elim h61181 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h111292 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step111318 (p3212 p4207 p4209 p5092 p6008 : Prop)
    (h108401 : (¬ p5092) ∨ (¬ p4207) ∨ (¬ p6008) ∨ (¬ p4209) ∨ (¬ p3212))
    (h8576 : p4207 ∨ (¬ p5092))
    : (¬ p5092) ∨ (¬ p6008) ∨ (¬ p4209) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4207) := (Or.elim h108401 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h8576 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111319 (p2122 p2707 p2829 p3426 : Prop)
    (h88279 : p2707 ∨ (¬ p2829) ∨ (¬ p3426))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ p2707 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3426) := (Or.elim h88279 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96484 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111320 (p2122 p2774 p3425 p3426 : Prop)
    (h4943 : (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3426))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3426) := (Or.elim h4943 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h96484 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111321 (p2122 p3426 p3587 p3985 : Prop)
    (h37269 : (¬ p3426) ∨ p3587 ∨ (¬ p3985))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ p3587 ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3587) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3426) := (Or.elim h37269 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96484 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111322 (p2122 p3426 p4426 p4781 : Prop)
    (h19546 : (¬ p3426) ∨ (¬ p4426) ∨ p4781)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ p4781 ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4781) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3426) := (Or.elim h19546 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96484 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111323 (p2122 p2396 p2819 p3426 p3434 : Prop)
    (h89628 : (¬ p3434) ∨ (¬ p3426) ∨ p2396 ∨ p2819)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p3434) ∨ p2819 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3426) := (Or.elim h89628 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111324 (p2122 p2295 p3426 p4253 p4260 : Prop)
    (h107196 : (¬ p4260) ∨ (¬ p4253) ∨ (¬ p3426) ∨ p2295)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p4253) ∨ (¬ p4260) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3426) := (Or.elim h107196 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111326 (p2122 p2177 p2307 p2717 p2782 p3426 : Prop)
    (h89191 : (¬ p2717) ∨ (¬ p3426) ∨ p2177 ∨ (¬ p2782) ∨ p2307)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ p2177 ∨ p2307 ∨ (¬ p2782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3426) := (Or.elim h89191 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111327 (p2122 p2177 p2608 p2717 p2829 p3426 : Prop)
    (h89193 : (¬ p2717) ∨ (¬ p2829) ∨ p2177 ∨ (¬ p3426) ∨ (¬ p2608))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p2608) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3426) := (Or.elim h89193 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111328 (p2122 p2177 p2717 p3426 p3654 p3917 : Prop)
    (h89198 : (¬ p3917) ∨ (¬ p3654) ∨ (¬ p3426) ∨ p2177 ∨ (¬ p2717))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p3917) ∨ p2177 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3426) := (Or.elim h89198 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111329 (p2122 p2717 p2881 p3323 p3426 p3917 : Prop)
    (h89215 : (¬ p2717) ∨ (¬ p3917) ∨ (¬ p3323) ∨ p2881 ∨ (¬ p3426))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p3917) ∨ p2881 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3426) := (Or.elim h89215 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111332 (p2122 p2132 p2284 p3425 p3426 p4428 p4906 : Prop)
    (h105632 : p4906)
    (h62414 : (¬ p2132) ∨ (¬ p2284) ∨ (¬ p3425) ∨ (¬ p3426) ∨ (¬ p4428) ∨ (¬ p4906))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2132) ∨ (¬ p4428) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4906 := h105632;
    let u6 : (¬ p3426) := (Or.elim h62414 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111334 (p2122 p2318 p2341 p2717 p3309 p3426 p4867 : Prop)
    (h106410 : p4867)
    (h89225 : (¬ p2717) ∨ p2341 ∨ (¬ p3426) ∨ p3309 ∨ (¬ p2318) ∨ (¬ p4867))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ p2341 ∨ p3309 ∨ (¬ p2318) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4867 := h106410;
    let u6 : (¬ p3426) := (Or.elim h89225 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111337 (p2122 p2933 p3389 p3426 p3434 p3631 p4375 : Prop)
    (h95733 : (¬ p2933) ∨ (¬ p3426) ∨ (¬ p4375) ∨ p3389 ∨ (¬ p3434) ∨ p3631)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ p3631 ∨ p3389 ∨ (¬ p2933) ∨ (¬ p4375) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3426) := (Or.elim h95733 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111341 (p2122 p2274 p2341 p2717 p3426 p3552 p4155 p4401 : Prop)
    (h89226 : (¬ p3552) ∨ (¬ p2717) ∨ p2274 ∨ p2341 ∨ (¬ p4401) ∨ (¬ p3426) ∨ (¬ p4155))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ p2341 ∨ (¬ p4401) ∨ p2274 ∨ (¬ p3552) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3426) := (Or.elim h89226 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111342 (p2122 p2373 p2417 p2441 p3426 p3434 p4428 p4509 : Prop)
    (h105392 : p4509)
    (h89575 : (¬ p3434) ∨ p2417 ∨ (¬ p4428) ∨ (¬ p4509) ∨ (¬ p3426) ∨ (¬ p2373) ∨ (¬ p2441))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p3434) ∨ (¬ p4428) ∨ p2417 ∨ (¬ p2441) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4509 := h105392;
    let u7 : (¬ p3426) := (Or.elim h89575 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111343 (p2122 p2449 p3156 p3426 p3434 p4386 p4428 p4509 : Prop)
    (h105392 : p4509)
    (h91249 : (¬ p3434) ∨ p2449 ∨ (¬ p3156) ∨ (¬ p4386) ∨ (¬ p4509) ∨ (¬ p4428) ∨ (¬ p3426))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p3434) ∨ (¬ p4428) ∨ (¬ p3156) ∨ p2449 ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4509 := h105392;
    let u7 : (¬ p3426) := (Or.elim h91249 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => r5))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111345 (p2122 p2318 p2553 p2717 p3426 p3527 p3543 p5225 : Prop)
    (h105495 : p5225)
    (h95699 : (¬ p3543) ∨ (¬ p2717) ∨ (¬ p2318) ∨ p3527 ∨ p2553 ∨ (¬ p5225) ∨ (¬ p3426))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ p3527 ∨ (¬ p2318) ∨ (¬ p3543) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5225 := h105495;
    let u7 : (¬ p3426) := (Or.elim h95699 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111351 (p2122 p2177 p2427 p2774 p2850 p3367 p3426 p3527 p4424 p4559 : Prop)
    (h105701 : p4559)
    (h93504 : (¬ p2774) ∨ p2850 ∨ (¬ p4559) ∨ (¬ p3426) ∨ p2427 ∨ (¬ p3527) ∨ (¬ p4424) ∨ p2177 ∨ p3367)
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2774) ∨ p2427 ∨ p3367 ∨ p2177 ∨ p2850 ∨ (¬ p3527) ∨ (¬ p4424) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4559 := h105701;
    let u9 : (¬ p3426) := (Or.elim h93504 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111352 (p2122 p2192 p2210 p2274 p2341 p2717 p3426 p3564 p4342 p4620 p5210 : Prop)
    (h89258 : (¬ p2717) ∨ (¬ p3426) ∨ p3564 ∨ (¬ p4620) ∨ (¬ p4342) ∨ p2341 ∨ (¬ p2274) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p5210))
    (h96484 : p3426 ∨ (¬ p2122))
    : (¬ p2122) ∨ p3564 ∨ (¬ p2717) ∨ (¬ p2192) ∨ p2341 ∨ (¬ p2274) ∨ (¬ p2210) ∨ (¬ p4342) ∨ (¬ p4620) ∨ (¬ p5210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3426) := (Or.elim h89258 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96484 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111356 (p3005 p3256 p3609 p4967 : Prop)
    (h95182 : p3609 ∨ (¬ p3256) ∨ (¬ p4967))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ p3609 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4967) := (Or.elim h95182 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h95976 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111358 (p3005 p3537 p4288 p4967 : Prop)
    (h109685 : (¬ p3537) ∨ p4288 ∨ (¬ p4967))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3537) ∨ p4288 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4288) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4967) := (Or.elim h109685 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h95976 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111360 (p2098 p3005 p3166 p4236 p4967 : Prop)
    (h95174 : (¬ p4236) ∨ (¬ p2098) ∨ (¬ p4967) ∨ p3166)
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ p3166 ∨ (¬ p4236) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4967) := (Or.elim h95174 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111362 (p2098 p2696 p3005 p3256 p3266 p4967 : Prop)
    (h82895 : (¬ p2098) ∨ (¬ p3256) ∨ (¬ p4967) ∨ (¬ p3266) ∨ p2696)
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3266) ∨ p2696 ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4967) := (Or.elim h82895 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111363 (p2098 p2696 p3005 p3146 p3256 p4967 : Prop)
    (h82897 : (¬ p2098) ∨ (¬ p3256) ∨ p2696 ∨ p3146 ∨ (¬ p4967))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ p3146 ∨ (¬ p3256) ∨ p2696 ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4967) := (Or.elim h82897 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111366 (p2630 p2737 p3005 p3537 p4967 p5011 : Prop)
    (h89795 : (¬ p4967) ∨ (¬ p3537) ∨ p2630 ∨ (¬ p5011) ∨ p2737)
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3537) ∨ p2630 ∨ p2737 ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4967) := (Or.elim h89795 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111367 (p3005 p3537 p3858 p4967 p5590 p5600 : Prop)
    (h109692 : (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5590) ∨ p5600 ∨ (¬ p3858))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3537) ∨ (¬ p5590) ∨ p5600 ∨ (¬ p3858) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p5600) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4967) := (Or.elim h109692 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111370 (p2245 p2630 p2737 p3005 p3166 p3537 p4967 : Prop)
    (h95173 : (¬ p2245) ∨ (¬ p4967) ∨ (¬ p3537) ∨ p2737 ∨ p3166 ∨ p2630)
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3537) ∨ (¬ p2245) ∨ p3166 ∨ p2737 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4967) := (Or.elim h95173 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111371 (p2696 p2737 p3005 p3256 p3537 p3589 p4967 : Prop)
    (h95181 : (¬ p3537) ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p4967) ∨ p2737 ∨ (¬ p3589))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3537) ∨ (¬ p3256) ∨ p2737 ∨ (¬ p2696) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4967) := (Or.elim h95181 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111375 (p2528 p3005 p3609 p3919 p3931 p4383 p4967 p5564 : Prop)
    (h93657 : (¬ p3931) ∨ p3609 ∨ (¬ p3919) ∨ (¬ p2528) ∨ (¬ p4967) ∨ (¬ p5564) ∨ (¬ p4383))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p5564) ∨ (¬ p4383) ∨ (¬ p3931) ∨ (¬ p3919) ∨ (¬ p2528) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4967) := (Or.elim h93657 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111377 (p2241 p2295 p2553 p2797 p3005 p3189 p3564 p3609 p4330 p4967 : Prop)
    (h106329 : p4330)
    (h79417 : p3609 ∨ (¬ p3564) ∨ p2553 ∨ (¬ p2797) ∨ p2241 ∨ p3189 ∨ (¬ p4330) ∨ (¬ p4967) ∨ (¬ p2295))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3564) ∨ p2553 ∨ (¬ p2295) ∨ (¬ p2797) ∨ p3189 ∨ p2241 ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    let u9 : (¬ p4967) := (Or.elim h79417 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111387 (p3005 p3166 p3266 p3366 p3379 p3399 p3609 p4075 p4236 p4376 p4826 p4967 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h101613 : (¬ p4075) ∨ p3609 ∨ (¬ p4376) ∨ p3379 ∨ (¬ p4236) ∨ (¬ p4826) ∨ p3266 ∨ (¬ p3366) ∨ (¬ p3399) ∨ p3166 ∨ (¬ p4967))
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p3166 ∨ p3609 ∨ p3266 ∨ (¬ p4236) ∨ (¬ p4075) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p4826 := h105444;
    let u11 : (¬ p4967) := (Or.elim h101613 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => r9))))))))))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111390 (p2156 p2563 p2696 p2982 p3005 p3256 p3366 p3537 p3645 p4030 p4202 p4752 p4967 p5059 : Prop)
    (h105434 : p4752)
    (h85649 : (¬ p4967) ∨ (¬ p3366) ∨ (¬ p2563) ∨ (¬ p3256) ∨ p2156 ∨ (¬ p5059) ∨ (¬ p4202) ∨ (¬ p3537) ∨ (¬ p4030) ∨ (¬ p3645) ∨ (¬ p4752) ∨ p2982 ∨ p2696)
    (h95976 : p4967 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3256) ∨ p2982 ∨ (¬ p2563) ∨ p2696 ∨ p2156 ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3645) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4752 := h105434;
    let u13 : (¬ p4967) := (Or.elim h85649 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u2 q11))) (fun r11 => (False.elim (u4 r11))))))))))))))))))))))))));
    (Or.elim h95976 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111391 (p2598 p3201 p3425 p3686 : Prop)
    (h88882 : (¬ p3686) ∨ p2598 ∨ p3425)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p3425 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3686) := (Or.elim h88882 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h101932 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111393 (p3201 p3686 p4752 p4782 : Prop)
    (h105434 : p4752)
    (h31255 : (¬ p3686) ∨ (¬ p4752) ∨ p4782)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p4782 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4782) := (fun h => hn (Or.inr h));
    let u2 : p4752 := h105434;
    let u3 : (¬ p3686) := (Or.elim h31255 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h101932 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111394 (p2922 p3201 p3590 p3686 p4106 : Prop)
    (h19124 : (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3686) ∨ (¬ p4106))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p2922) ∨ (¬ p4106) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3686) := (Or.elim h19124 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111395 (p3201 p3367 p3576 p3686 p3687 : Prop)
    (h88086 : (¬ p3687) ∨ (¬ p3576) ∨ p3367 ∨ (¬ p3686))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p3576) ∨ p3367 ∨ (¬ p3687) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3686) := (Or.elim h88086 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h101932 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111396 (p2753 p3201 p3367 p3425 p3686 : Prop)
    (h88889 : (¬ p2753) ∨ (¬ p3686) ∨ p3425 ∨ p3367)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p3425 ∨ (¬ p2753) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3686) := (Or.elim h88889 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111398 (p2264 p2717 p2807 p3201 p3422 p3686 : Prop)
    (h88880 : p2717 ∨ (¬ p3422) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p3686))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p2717 ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3686) := (Or.elim h88880 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111399 (p2417 p2850 p3201 p3434 p3686 p4644 : Prop)
    (h105411 : p4644)
    (h88891 : (¬ p2417) ∨ p3434 ∨ (¬ p2850) ∨ (¬ p4644) ∨ (¬ p3686))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p2417) ∨ p3434 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    let u5 : (¬ p3686) := (Or.elim h88891 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111400 (p2437 p2717 p2911 p3201 p3686 p4750 : Prop)
    (h105433 : p4750)
    (h97041 : p2717 ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4750))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p2717 ∨ (¬ p2911) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p3686) := (Or.elim h97041 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111401 (p2417 p2437 p3201 p3434 p3686 p4750 : Prop)
    (h105433 : p4750)
    (h98033 : (¬ p2417) ∨ p3434 ∨ (¬ p4750) ∨ (¬ p2437) ∨ (¬ p3686))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ p3434 ∨ (¬ p2437) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p3686) := (Or.elim h98033 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111403 (p2717 p2927 p3201 p3389 p3527 p3686 p4730 : Prop)
    (h106074 : p4730)
    (h85135 : (¬ p3527) ∨ (¬ p2927) ∨ (¬ p4730) ∨ (¬ p3389) ∨ (¬ p3686) ∨ p2717)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p3527) ∨ (¬ p3389) ∨ p2717 ∨ (¬ p2927) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4730 := h106074;
    let u6 : (¬ p3686) := (Or.elim h85135 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111404 (p2341 p2717 p2922 p3201 p3575 p3686 p5217 : Prop)
    (h105493 : p5217)
    (h88888 : (¬ p2341) ∨ (¬ p3575) ∨ (¬ p2922) ∨ (¬ p3686) ∨ p2717 ∨ (¬ p5217))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p3575) ∨ p2717 ∨ (¬ p2341) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5217 := h105493;
    let u6 : (¬ p3686) := (Or.elim h88888 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111406 (p2264 p2717 p2751 p2996 p3201 p3364 p3686 : Prop)
    (h106343 : p2751)
    (h97089 : (¬ p3364) ∨ (¬ p2751) ∨ (¬ p3686) ∨ p2996 ∨ (¬ p2264) ∨ p2717)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p2264) ∨ p2996 ∨ p2717 ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p3686) := (Or.elim h97089 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111409 (p2850 p2927 p3201 p3434 p3516 p3543 p3686 p4644 : Prop)
    (h105411 : p4644)
    (h87841 : p3434 ∨ (¬ p3543) ∨ (¬ p2927) ∨ (¬ p2850) ∨ (¬ p3516) ∨ (¬ p4644) ∨ (¬ p3686))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p3516) ∨ (¬ p2927) ∨ p3434 ∨ (¬ p2850) ∨ (¬ p3543) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4644 := h105411;
    let u7 : (¬ p3686) := (Or.elim h87841 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111417 (p2509 p2528 p2651 p3201 p3361 p3422 p3487 p3686 p4781 : Prop)
    (h88524 : p2528 ∨ (¬ p2509) ∨ (¬ p3487) ∨ (¬ p3361) ∨ (¬ p3686) ∨ p2651 ∨ (¬ p3422) ∨ (¬ p4781))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p4781) ∨ p2528 ∨ (¬ p3422) ∨ (¬ p2509) ∨ p2651 ∨ (¬ p3487) ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3686) := (Or.elim h88524 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111421 (p2192 p2210 p2274 p2598 p2717 p2911 p3201 p3686 p4712 p4736 : Prop)
    (h105431 : p4736)
    (h105422 : p4712)
    (h81022 : (¬ p3686) ∨ p2717 ∨ (¬ p2911) ∨ (¬ p2210) ∨ (¬ p2192) ∨ p2598 ∨ (¬ p2274) ∨ (¬ p4712) ∨ (¬ p4736))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2911) ∨ p2598 ∨ p2717 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4712 := h105422;
    let u9 : (¬ p3686) := (Or.elim h81022 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111423 (p2331 p3201 p3323 p3333 p3362 p3389 p3461 p3686 p3868 p4423 p4789 : Prop)
    (h105646 : p4789)
    (h75071 : (¬ p4423) ∨ (¬ p3868) ∨ p2331 ∨ (¬ p3333) ∨ p3461 ∨ p3323 ∨ (¬ p3389) ∨ (¬ p3362) ∨ (¬ p3686) ∨ (¬ p4789))
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p4423) ∨ p3461 ∨ (¬ p3868) ∨ p3323 ∨ (¬ p3333) ∨ (¬ p3362) ∨ p2331 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4789 := h105646;
    let u10 : (¬ p3686) := (Or.elim h75071 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111426 (p2249 p2274 p2331 p2996 p3201 p3276 p3333 p3686 p3737 p3922 p4325 p4435 : Prop)
    (h106513 : p2249)
    (h96713 : (¬ p3737) ∨ (¬ p4435) ∨ (¬ p2249) ∨ (¬ p3922) ∨ p2274 ∨ (¬ p3276) ∨ (¬ p3686) ∨ (¬ p3333) ∨ p2996 ∨ p4325 ∨ p2331)
    (h101932 : p3686 ∨ p3201)
    : p3201 ∨ (¬ p4435) ∨ p4325 ∨ p2996 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3922) ∨ (¬ p3737) ∨ p2274 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4325) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2249 := h106513;
    let u11 : (¬ p3686) := (Or.elim h96713 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (u9 r9))))))))))))))))))))));
    (Or.elim h101932 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111428 (p2192 p2972 p3125 p4334 : Prop)
    (h17454 : (¬ p2192) ∨ p2972 ∨ (¬ p4334))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ (¬ p2192) ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4334) := (Or.elim h17454 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96319 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111429 (p2156 p3125 p4032 p4334 : Prop)
    (h20722 : (¬ p2156) ∨ (¬ p4032) ∨ (¬ p4334))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4334) := (Or.elim h20722 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h96319 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111430 (p2860 p3105 p3125 p4334 : Prop)
    (h84498 : (¬ p4334) ∨ p3105 ∨ (¬ p2860))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p3105 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4334) := (Or.elim h84498 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96319 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111431 (p2563 p2982 p3125 p4334 : Prop)
    (h92060 : p2982 ∨ (¬ p4334) ∨ (¬ p2563))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p2982 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4334) := (Or.elim h92060 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96319 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111432 (p2284 p3115 p3125 p4334 : Prop)
    (h93027 : p3115 ∨ (¬ p4334) ∨ (¬ p2284))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p3115 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4334) := (Or.elim h93027 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96319 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111433 (p2156 p2972 p3125 p3370 p4334 : Prop)
    (h37562 : (¬ p2156) ∨ p2972 ∨ (¬ p3370) ∨ (¬ p4334))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p2972 ∨ (¬ p3370) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4334) := (Or.elim h37562 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96319 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111441 (p2274 p3125 p3461 p3680 p4334 p4624 : Prop)
    (h105408 : p4624)
    (h82511 : (¬ p3680) ∨ p3461 ∨ (¬ p4334) ∨ (¬ p4624) ∨ p2274)
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p2274 ∨ (¬ p3680) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4334) := (Or.elim h82511 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96319 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111442 (p3125 p3461 p3564 p3680 p3958 p4334 : Prop)
    (h105378 : p3958)
    (h82512 : (¬ p3680) ∨ p3461 ∨ (¬ p4334) ∨ p3564 ∨ (¬ p3958))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p3461 ∨ (¬ p3680) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p4334) := (Or.elim h82512 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96319 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111446 (p2427 p2982 p3125 p3276 p3680 p4334 : Prop)
    (h109967 : p2982 ∨ (¬ p4334) ∨ (¬ p3680) ∨ p3276 ∨ (¬ p2427))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ p2982 ∨ (¬ p3680) ∨ p3276 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4334) := (Or.elim h109967 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96319 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111447 (p2284 p2946 p3125 p3322 p3461 p3680 p4334 : Prop)
    (h82513 : p3461 ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p2284) ∨ (¬ p3322) ∨ (¬ p4334))
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ (¬ p3322) ∨ p3461 ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4334) := (Or.elim h82513 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h96319 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111460 (p2156 p2417 p2608 p2707 p3125 p3461 p3680 p4106 p4334 p4521 p4621 : Prop)
    (h105407 : p4621)
    (h93103 : (¬ p4334) ∨ (¬ p3680) ∨ (¬ p4106) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p4621) ∨ p3461 ∨ p2417 ∨ (¬ p4521) ∨ p2608)
    (h96319 : p4334 ∨ (¬ p3125))
    : (¬ p3125) ∨ (¬ p3680) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3461 ∨ p2417 ∨ (¬ p4106) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4621 := h105407;
    let u10 : (¬ p4334) := (Or.elim h93103 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h96319 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111465 (p2098 p2598 p3641 p5368 : Prop)
    (h77783 : (¬ p2098) ∨ (¬ p5368) ∨ p2598)
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2098) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5368) := (Or.elim h77783 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h97919 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111468 (p2470 p2528 p3609 p3641 p4730 p5368 : Prop)
    (h106074 : p4730)
    (h77792 : (¬ p2470) ∨ (¬ p5368) ∨ (¬ p2528) ∨ p3609 ∨ (¬ p4730))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2470) ∨ (¬ p2528) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p5368) := (Or.elim h77792 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111469 (p3193 p3590 p3609 p3641 p4695 p5368 : Prop)
    (h77793 : p3193 ∨ p3609 ∨ (¬ p3590) ∨ (¬ p4695) ∨ (¬ p5368))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ p3193 ∨ p3609 ∨ (¬ p3590) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5368) := (Or.elim h77793 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111472 (p2510 p2528 p2553 p3367 p3609 p3641 p5368 : Prop)
    (h75601 : (¬ p2510) ∨ p3609 ∨ p3367 ∨ p2553 ∨ (¬ p2528) ∨ (¬ p5368))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2510) ∨ p2553 ∨ (¬ p2528) ∨ p3609 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5368) := (Or.elim h75601 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111473 (p2528 p2573 p3422 p3609 p3641 p3905 p5368 : Prop)
    (h77787 : p3609 ∨ p2573 ∨ (¬ p3905) ∨ (¬ p3422) ∨ (¬ p5368) ∨ (¬ p2528))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ p2573 ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p2528) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5368) := (Or.elim h77787 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111476 (p2088 p2475 p3083 p3609 p3641 p4750 p5368 : Prop)
    (h105433 : p4750)
    (h90092 : p3609 ∨ (¬ p5368) ∨ (¬ p3083) ∨ (¬ p4750) ∨ (¬ p2475) ∨ (¬ p2088))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ p3609 ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : (¬ p5368) := (Or.elim h90092 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111477 (p2440 p2528 p3609 p3641 p4355 p4750 p5368 : Prop)
    (h105433 : p4750)
    (h97098 : p3609 ∨ (¬ p2528) ∨ (¬ p4355) ∨ p2440 ∨ (¬ p4750) ∨ (¬ p5368))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p4355) ∨ p3609 ∨ (¬ p2528) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : (¬ p5368) := (Or.elim h97098 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111491 (p2187 p2274 p2307 p2528 p2598 p2781 p3609 p3641 p4384 p5368 : Prop)
    (h106167 : p4384)
    (h96916 : (¬ p2307) ∨ (¬ p5368) ∨ p2274 ∨ (¬ p4384) ∨ (¬ p2781) ∨ (¬ p2187) ∨ (¬ p2528) ∨ p2598 ∨ p3609)
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2187) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4384 := h106167;
    let u9 : (¬ p5368) := (Or.elim h96916 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111492 (p2210 p2528 p2598 p2881 p2891 p3609 p3641 p4438 p4736 p5368 : Prop)
    (h105431 : p4736)
    (h97169 : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p4438) ∨ p3609 ∨ (¬ p2528) ∨ (¬ p4736) ∨ (¬ p5368) ∨ (¬ p2210) ∨ p2598)
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2881) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : (¬ p5368) := (Or.elim h97169 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111494 (p2156 p2177 p2274 p2528 p3367 p3370 p3609 p3641 p4377 p4438 p5368 : Prop)
    (h106170 : p4377)
    (h75594 : (¬ p3370) ∨ (¬ p2274) ∨ (¬ p2156) ∨ (¬ p4438) ∨ (¬ p4377) ∨ (¬ p5368) ∨ (¬ p2528) ∨ (¬ p2177) ∨ p3367 ∨ p3609)
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ p3609 ∨ (¬ p3370) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2528) ∨ p3367 ∨ (¬ p2177) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    let u10 : (¬ p5368) := (Or.elim h75594 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (u1 r8))))))))))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111495 (p2187 p2210 p2528 p3093 p3367 p3609 p3641 p4377 p4384 p4516 p5368 : Prop)
    (h106170 : p4377)
    (h106167 : p4384)
    (h77789 : (¬ p4516) ∨ (¬ p3093) ∨ (¬ p2187) ∨ p3367 ∨ p2210 ∨ p3609 ∨ (¬ p2528) ∨ (¬ p5368) ∨ (¬ p4377) ∨ (¬ p4384))
    (h97919 : p5368 ∨ p3641)
    : p3641 ∨ (¬ p2187) ∨ p3609 ∨ (¬ p2528) ∨ p2210 ∨ (¬ p3093) ∨ (¬ p4516) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    let u9 : p4384 := h106167;
    let u10 : (¬ p5368) := (Or.elim h77789 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h97919 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111503 (p3276 p3461 p3564 p4022 : Prop)
    (h98814 : (¬ p3276) ∨ p3461 ∨ (¬ p4022))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3461 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4022) := (Or.elim h98814 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h90153 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111504 (p2584 p3355 p3564 p3654 p4022 : Prop)
    (h22173 : (¬ p2584) ∨ p3355 ∨ (¬ p3654) ∨ (¬ p4022))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3654) ∨ p3355 ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3355) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4022) := (Or.elim h22173 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h90153 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111505 (p2352 p3564 p3746 p3990 p4022 : Prop)
    (h5990 : (¬ p2352) ∨ (¬ p3746) ∨ (¬ p3990) ∨ (¬ p4022))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3746) ∨ (¬ p2352) ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4022) := (Or.elim h5990 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h90153 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111506 (p3125 p3422 p3564 p3958 p4022 p5160 : Prop)
    (h105378 : p3958)
    (h51970 : (¬ p3125) ∨ (¬ p3422) ∨ (¬ p3958) ∨ (¬ p4022) ∨ (¬ p5160))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p5160) ∨ (¬ p3125) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p4022) := (Or.elim h51970 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111507 (p2493 p3016 p3193 p3461 p3564 p4022 : Prop)
    (h85727 : p3461 ∨ (¬ p3193) ∨ (¬ p2493) ∨ (¬ p4022) ∨ p3016)
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3461 ∨ (¬ p3193) ∨ p3016 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4022) := (Or.elim h85727 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111508 (p2295 p2493 p3193 p3323 p3564 p4022 : Prop)
    (h85800 : (¬ p3323) ∨ (¬ p3193) ∨ (¬ p2493) ∨ (¬ p4022) ∨ p2295)
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3323) ∨ p2295 ∨ (¬ p3193) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4022) := (Or.elim h85800 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111511 (p3016 p3343 p3483 p3564 p4022 p5225 : Prop)
    (h105495 : p5225)
    (h90258 : p3343 ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p3016) ∨ (¬ p5225))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3343 ∨ (¬ p3483) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    let u5 : (¬ p4022) := (Or.elim h90258 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111513 (p2493 p2573 p3346 p3461 p3564 p4022 : Prop)
    (h99324 : p3461 ∨ (¬ p4022) ∨ (¬ p3346) ∨ p2493 ∨ (¬ p2573))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p2573) ∨ (¬ p3346) ∨ p2493 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4022) := (Or.elim h99324 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111515 (p3016 p3125 p3343 p3564 p3958 p4022 : Prop)
    (h105378 : p3958)
    (h101274 : (¬ p4022) ∨ (¬ p3125) ∨ (¬ p3958) ∨ (¬ p3016) ∨ p3343)
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3343 ∨ (¬ p3125) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p4022) := (Or.elim h101274 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111516 (p2553 p3016 p3343 p3564 p4022 p4620 : Prop)
    (h101279 : p3343 ∨ (¬ p2553) ∨ (¬ p4022) ∨ (¬ p4620) ∨ (¬ p3016))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3343 ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4022) := (Or.elim h101279 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111521 (p2187 p2406 p3125 p3193 p3564 p4022 p4138 : Prop)
    (h90969 : (¬ p3193) ∨ (¬ p3125) ∨ (¬ p2406) ∨ p2187 ∨ (¬ p4022) ∨ (¬ p4138))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3125) ∨ (¬ p3193) ∨ (¬ p2406) ∨ p2187 ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4022) := (Or.elim h90969 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111522 (p2573 p3193 p3422 p3461 p3519 p3564 p4022 : Prop)
    (h101462 : p3461 ∨ (¬ p3519) ∨ p3422 ∨ (¬ p2573) ∨ (¬ p4022) ∨ (¬ p3193))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3422 ∨ (¬ p3519) ∨ p3461 ∨ (¬ p2573) ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4022) := (Or.elim h101462 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111523 (p2573 p2655 p3016 p3343 p3461 p3564 p4022 : Prop)
    (h101853 : p3461 ∨ p3343 ∨ (¬ p2655) ∨ p2573 ∨ (¬ p3016) ∨ (¬ p4022))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3343 ∨ p2573 ∨ p3461 ∨ (¬ p2655) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4022) := (Or.elim h101853 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111524 (p2573 p2668 p3346 p3564 p3990 p4022 p4976 : Prop)
    (h105465 : p4976)
    (h61180 : (¬ p2573) ∨ (¬ p2668) ∨ (¬ p3346) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4976))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3346) ∨ (¬ p3990) ∨ (¬ p2668) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4976 := h105465;
    let u6 : (¬ p4022) := (Or.elim h61180 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111531 (p2132 p2383 p2781 p2870 p3246 p3266 p3276 p3564 p3990 p4022 p4669 : Prop)
    (h105415 : p4669)
    (h86672 : p3266 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p4022) ∨ (¬ p2383) ∨ (¬ p3990) ∨ (¬ p3276) ∨ (¬ p2781) ∨ p2132 ∨ p3246)
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3276) ∨ (¬ p2383) ∨ p3246 ∨ (¬ p2781) ∨ p2870 ∨ p3266 ∨ (¬ p3990) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4669 := h105415;
    let u10 : (¬ p4022) := (Or.elim h86672 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u3 r8))))))))))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111534 (p2088 p2249 p2474 p2651 p3189 p3193 p3256 p3363 p3422 p3461 p3487 p3564 p4022 : Prop)
    (h106513 : p2249)
    (h87667 : (¬ p3189) ∨ p3461 ∨ (¬ p2249) ∨ (¬ p3422) ∨ (¬ p3193) ∨ (¬ p3363) ∨ (¬ p4022) ∨ p2651 ∨ (¬ p3256) ∨ p2088 ∨ (¬ p3487) ∨ (¬ p2474))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p3461 ∨ (¬ p3189) ∨ (¬ p3256) ∨ p2651 ∨ (¬ p3422) ∨ p2088 ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p3363) ∨ (¬ p2474) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2249 := h106513;
    let u12 : (¬ p4022) := (Or.elim h87667 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u6 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u10))))))))))))))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111535 (p2132 p2252 p2573 p2655 p2750 p2753 p2870 p3016 p3246 p3343 p3564 p4022 p4625 : Prop)
    (h106345 : p2750)
    (h106455 : p4625)
    (h90707 : (¬ p2753) ∨ (¬ p4625) ∨ (¬ p4022) ∨ (¬ p2132) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p2870) ∨ (¬ p2750) ∨ (¬ p2252) ∨ p2573 ∨ p3343 ∨ (¬ p3246))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ p2573 ∨ (¬ p2252) ∨ (¬ p3246) ∨ (¬ p2132) ∨ (¬ p3016) ∨ (¬ p2870) ∨ (¬ p2655) ∨ (¬ p2753) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : p4625 := h106455;
    let u12 : (¬ p4022) := (Or.elim h90707 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u9 q10))) (fun r10 => (False.elim (r10 u3))))))))))))))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111537 (p2246 p2264 p2459 p2573 p2744 p2807 p3366 p3422 p3564 p3905 p4022 p4604 p5160 : Prop)
    (h106503 : p2744)
    (h106293 : p4604)
    (h99799 : (¬ p3905) ∨ (¬ p2246) ∨ p2573 ∨ (¬ p5160) ∨ (¬ p4604) ∨ (¬ p2744) ∨ (¬ p3422) ∨ (¬ p4022) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p2459) ∨ (¬ p3366))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p5160) ∨ (¬ p3422) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p3905) ∨ (¬ p2459) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4604 := h106293;
    let u12 : (¬ p4022) := (Or.elim h99799 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u5))))))))))))))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111538 (p2246 p2573 p2744 p2901 p2946 p3246 p3366 p3422 p3564 p3905 p4022 p4625 p5160 : Prop)
    (h106503 : p2744)
    (h106455 : p4625)
    (h101636 : (¬ p3246) ∨ (¬ p4625) ∨ (¬ p5160) ∨ (¬ p2744) ∨ (¬ p4022) ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p2246) ∨ p2573 ∨ (¬ p3366))
    (h90153 : p4022 ∨ p3564)
    : p3564 ∨ (¬ p3246) ∨ (¬ p5160) ∨ (¬ p2901) ∨ (¬ p3422) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p3905) ∨ (¬ p2946) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4625 := h106455;
    let u12 : (¬ p4022) := (Or.elim h101636 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u9 q10))) (fun r10 => (False.elim (r10 u5))))))))))))))))))))))));
    (Or.elim h90153 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111540 (p2098 p2774 p2819 p4078 : Prop)
    (h89711 : (¬ p2098) ∨ p2774 ∨ (¬ p4078))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2098) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4078) := (Or.elim h89711 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102447 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111541 (p2819 p2829 p3537 p4078 : Prop)
    (h89756 : (¬ p3537) ∨ p2829 ∨ (¬ p4078))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p3537) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4078) := (Or.elim h89756 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h102447 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111543 (p2363 p2383 p2788 p2819 p3609 p4078 : Prop)
    (h105375 : p2788)
    (h83966 : p3609 ∨ (¬ p2383) ∨ (¬ p4078) ∨ (¬ p2788) ∨ (¬ p2363))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2383) ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2788 := h105375;
    let u5 : (¬ p4078) := (Or.elim h83966 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111544 (p2088 p2122 p2819 p3609 p4078 p4170 : Prop)
    (h90369 : p3609 ∨ (¬ p2122) ∨ (¬ p2088) ∨ (¬ p4078) ∨ (¬ p4170))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p3609 ∨ (¬ p4170) ∨ (¬ p2122) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4078) := (Or.elim h90369 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111545 (p2363 p2737 p2819 p2829 p3609 p4078 : Prop)
    (h90511 : p3609 ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2363) ∨ (¬ p4078))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p3609 ∨ (¬ p2363) ∨ p2829 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4078) := (Or.elim h90511 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111546 (p2363 p2608 p2819 p2829 p3609 p4078 : Prop)
    (h97095 : p2829 ∨ p3609 ∨ (¬ p2363) ∨ (¬ p4078) ∨ p2608)
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p3609 ∨ p2829 ∨ p2608 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4078) := (Or.elim h97095 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111547 (p2363 p2598 p2774 p2819 p3609 p4078 : Prop)
    (h97099 : p3609 ∨ p2774 ∨ (¬ p2363) ∨ (¬ p4078) ∨ (¬ p2598))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p3609 ∨ (¬ p2363) ∨ p2774 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4078) := (Or.elim h97099 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111549 (p2363 p2819 p2829 p3063 p3609 p4078 : Prop)
    (h109331 : (¬ p2829) ∨ (¬ p3063) ∨ p3609 ∨ (¬ p4078) ∨ (¬ p2363))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2829) ∨ (¬ p3063) ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4078) := (Or.elim h109331 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111551 (p2098 p2641 p2696 p2745 p2819 p4078 p4328 : Prop)
    (h105523 : p2745)
    (h93179 : (¬ p2098) ∨ p2641 ∨ (¬ p4078) ∨ (¬ p4328) ∨ p2696 ∨ (¬ p2745))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p2641 ∨ p2696 ∨ (¬ p4328) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    let u6 : (¬ p4078) := (Or.elim h93179 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111552 (p2088 p2187 p2819 p3609 p4078 p4170 p4889 : Prop)
    (h93424 : p3609 ∨ (¬ p2088) ∨ (¬ p4078) ∨ (¬ p4889) ∨ (¬ p4170) ∨ (¬ p2187))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p4170) ∨ (¬ p2187) ∨ (¬ p2088) ∨ p3609 ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4078) := (Or.elim h93424 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111556 (p2166 p2819 p2891 p3073 p3609 p4078 p4185 : Prop)
    (h111211 : (¬ p2166) ∨ (¬ p3073) ∨ (¬ p4078) ∨ (¬ p4185) ∨ p3609 ∨ p2891)
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2166) ∨ (¬ p3073) ∨ (¬ p4185) ∨ p3609 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4078) := (Or.elim h111211 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111565 (p2363 p2373 p2406 p2774 p2819 p3379 p3609 p4078 p4433 p4736 : Prop)
    (h105431 : p4736)
    (h106150 : p4433)
    (h86320 : p3609 ∨ (¬ p4078) ∨ (¬ p4433) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2363) ∨ (¬ p2373))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2373) ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2774 ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4433 := h106150;
    let u9 : (¬ p4078) := (Or.elim h86320 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111570 (p2264 p2363 p2696 p2742 p2819 p2829 p2996 p3609 p4078 p4503 : Prop)
    (h106530 : p4503)
    (h97100 : p2829 ∨ (¬ p2742) ∨ p2996 ∨ (¬ p4503) ∨ (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2363) ∨ p3609 ∨ (¬ p4078))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2264) ∨ p2996 ∨ p2829 ∨ p3609 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : (¬ p4078) := (Or.elim h97100 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111571 (p2241 p2363 p2774 p2819 p2992 p3156 p3609 p4078 p4433 p4736 : Prop)
    (h105431 : p4736)
    (h106150 : p4433)
    (h97118 : p2774 ∨ (¬ p2992) ∨ (¬ p4433) ∨ (¬ p2363) ∨ (¬ p4078) ∨ p3609 ∨ (¬ p2241) ∨ (¬ p3156) ∨ (¬ p4736))
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ p3609 ∨ (¬ p2992) ∨ (¬ p2363) ∨ p2774 ∨ (¬ p2241) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4433 := h106150;
    let u9 : (¬ p4078) := (Or.elim h97118 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111572 (p2166 p2210 p2241 p2363 p2744 p2774 p2819 p3366 p3609 p4078 p4433 : Prop)
    (h106503 : p2744)
    (h106150 : p4433)
    (h93841 : p3609 ∨ (¬ p4078) ∨ (¬ p3366) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2166) ∨ (¬ p4433) ∨ p2241 ∨ (¬ p2744) ∨ p2774)
    (h102447 : p4078 ∨ p2819)
    : p2819 ∨ (¬ p2166) ∨ p2241 ∨ (¬ p3366) ∨ (¬ p2210) ∨ p2774 ∨ (¬ p2363) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4433 := h106150;
    let u10 : (¬ p4078) := (Or.elim h93841 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u5 r8))))))))))))))))))));
    (Or.elim h102447 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111578 (p2528 p3266 p3276 p4695 : Prop)
    (h79534 : p3276 ∨ (¬ p3266) ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3276 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4695) := (Or.elim h79534 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96004 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111580 (p2459 p2528 p3083 p3343 p4695 : Prop)
    (h107100 : (¬ p3343) ∨ p3083 ∨ (¬ p4695) ∨ p2459)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2459 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4695) := (Or.elim h107100 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111581 (p2528 p3083 p3343 p4149 p4695 p5118 : Prop)
    (h105482 : p5118)
    (h74650 : p4149 ∨ (¬ p3343) ∨ p3083 ∨ (¬ p4695) ∨ (¬ p5118))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p4149 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    let u5 : (¬ p4695) := (Or.elim h74650 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111582 (p2088 p2478 p2509 p2528 p3193 p4695 : Prop)
    (h81702 : (¬ p2509) ∨ p3193 ∨ p2088 ∨ (¬ p2478) ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3193 ∨ (¬ p2509) ∨ p2088 ∨ (¬ p2478) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2478 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h81702 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111583 (p2363 p2470 p2528 p3355 p4384 p4695 : Prop)
    (h106167 : p4384)
    (h85004 : (¬ p4695) ∨ p2363 ∨ (¬ p3355) ∨ p2470 ∨ (¬ p4384))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2363 ∨ p2470 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4384 := h106167;
    let u5 : (¬ p4695) := (Or.elim h85004 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111584 (p2470 p2528 p3146 p3355 p4434 p4695 : Prop)
    (h106144 : p4434)
    (h85006 : (¬ p3355) ∨ p3146 ∨ (¬ p4434) ∨ p2470 ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3146 ∨ (¬ p3355) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4434 := h106144;
    let u5 : (¬ p4695) := (Or.elim h85006 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111585 (p2459 p2470 p2528 p3355 p4438 p4695 : Prop)
    (h85041 : (¬ p3355) ∨ (¬ p4438) ∨ p2459 ∨ p2470 ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2459 ∨ (¬ p4438) ∨ p2470 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h85041 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111586 (p2459 p2528 p3333 p3641 p4438 p4695 : Prop)
    (h95591 : (¬ p3333) ∨ (¬ p4438) ∨ p2459 ∨ (¬ p4695) ∨ p3641)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2459 ∨ p3641 ∨ (¬ p4438) ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h95591 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111587 (p2528 p3333 p3641 p4149 p4695 p5118 : Prop)
    (h105482 : p5118)
    (h95598 : p4149 ∨ (¬ p3333) ∨ p3641 ∨ (¬ p4695) ∨ (¬ p5118))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p4149 ∨ p3641 ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    let u5 : (¬ p4695) := (Or.elim h95598 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111589 (p2470 p2528 p3073 p3355 p4685 p4695 : Prop)
    (h96679 : (¬ p3355) ∨ p3073 ∨ p2470 ∨ (¬ p4685) ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3073 ∨ p2470 ∨ (¬ p3355) ∨ (¬ p4685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h96679 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111590 (p2528 p3083 p3146 p3343 p4434 p4695 : Prop)
    (h106144 : p4434)
    (h98672 : (¬ p3343) ∨ (¬ p4695) ∨ (¬ p4434) ∨ p3083 ∨ p3146)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3146 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4434 := h106144;
    let u5 : (¬ p4695) := (Or.elim h98672 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111593 (p2363 p2528 p2982 p3115 p3156 p4695 : Prop)
    (h111236 : p2982 ∨ p2363 ∨ (¬ p4695) ∨ (¬ p3115) ∨ p3156)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2982 ∨ p2363 ∨ (¬ p3115) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h111236 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111594 (p2528 p3193 p3590 p3609 p3641 p4695 : Prop)
    (h111469 : p3641 ∨ p3193 ∨ p3609 ∨ (¬ p3590) ∨ (¬ p4695))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p3641 ∨ p3193 ∨ p3609 ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4695) := (Or.elim h111469 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111595 (p2363 p2528 p2656 p3083 p3355 p4384 p4695 : Prop)
    (h106167 : p4384)
    (h74644 : p2363 ∨ (¬ p3355) ∨ (¬ p4695) ∨ p3083 ∨ (¬ p4384) ∨ (¬ p2656))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2363 ∨ p3083 ∨ (¬ p2656) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4384 := h106167;
    let u6 : (¬ p4695) := (Or.elim h74644 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111599 (p2363 p2528 p3527 p3631 p4133 p4636 p4695 : Prop)
    (h105712 : p4133)
    (h96042 : (¬ p3631) ∨ (¬ p4695) ∨ (¬ p4133) ∨ p3527 ∨ (¬ p4636) ∨ p2363)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ (¬ p3631) ∨ p3527 ∨ p2363 ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4695) := (Or.elim h96042 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111600 (p2088 p2528 p3083 p3343 p3858 p4685 p4695 : Prop)
    (h98451 : (¬ p3343) ∨ p3083 ∨ (¬ p4695) ∨ (¬ p4685) ∨ (¬ p3858) ∨ p2088)
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ (¬ p4685) ∨ p3083 ∨ (¬ p3343) ∨ (¬ p3858) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4695) := (Or.elim h98451 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111602 (p2363 p2528 p3083 p3343 p4133 p4383 p4695 : Prop)
    (h105712 : p4133)
    (h101288 : (¬ p4695) ∨ p2363 ∨ (¬ p4133) ∨ p3083 ∨ (¬ p4383) ∨ (¬ p3343))
    (h96004 : p4695 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2363 ∨ (¬ p4383) ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4695) := (Or.elim h101288 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96004 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111616 (p2829 p3367 p3422 p5220 : Prop)
    (h77760 : (¬ p2829) ∨ (¬ p5220) ∨ p3367)
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p2829) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5220) := (Or.elim h77760 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h97817 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111617 (p2598 p2774 p3422 p5220 : Prop)
    (h77767 : (¬ p2774) ∨ (¬ p5220) ∨ p2598)
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p2774) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5220) := (Or.elim h77767 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h97817 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111619 (p2819 p3422 p3641 p4157 p5220 : Prop)
    (h40808 : p2819 ∨ (¬ p3641) ∨ (¬ p4157) ∨ (¬ p5220))
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ p2819 ∨ (¬ p4157) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5220) := (Or.elim h40808 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h97817 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111620 (p2122 p2850 p3093 p3309 p3422 p5220 : Prop)
    (h77749 : (¬ p3309) ∨ (¬ p2850) ∨ (¬ p5220) ∨ p2122 ∨ (¬ p3093))
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ p2122 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5220) := (Or.elim h77749 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111621 (p2352 p2819 p3016 p3422 p4750 p5220 : Prop)
    (h105433 : p4750)
    (h77753 : (¬ p2352) ∨ (¬ p3016) ∨ (¬ p5220) ∨ (¬ p4750) ∨ p2819)
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ p2819 ∨ (¬ p3016) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p5220) := (Or.elim h77753 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111631 (p2122 p2553 p3422 p3641 p3660 p4610 p5220 : Prop)
    (h77766 : (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ p2122 ∨ (¬ p5220) ∨ (¬ p4610))
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p2553) ∨ p2122 ∨ (¬ p3660) ∨ (¬ p3641) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5220) := (Or.elim h77766 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111639 (p2122 p2307 p2498 p2850 p3422 p4715 p5016 p5220 : Prop)
    (h105423 : p4715)
    (h77763 : p2122 ∨ (¬ p5220) ∨ (¬ p2498) ∨ (¬ p4715) ∨ (¬ p2307) ∨ (¬ p5016) ∨ (¬ p2850))
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p2307) ∨ p2122 ∨ (¬ p2498) ∨ (¬ p5016) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4715 := h105423;
    let u7 : (¬ p5220) := (Or.elim h77763 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111648 (p2122 p2284 p2553 p2696 p2742 p2992 p3367 p3422 p4718 p5220 : Prop)
    (h105425 : p4718)
    (h97829 : (¬ p2992) ∨ (¬ p2742) ∨ (¬ p4718) ∨ (¬ p5220) ∨ (¬ p2696) ∨ (¬ p2284) ∨ (¬ p2553) ∨ p3367 ∨ p2122)
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p2553) ∨ p2122 ∨ (¬ p2284) ∨ (¬ p2742) ∨ p3367 ∨ (¬ p2992) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4718 := h105425;
    let u9 : (¬ p5220) := (Or.elim h97829 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111652 (p2573 p2850 p2946 p3146 p3156 p3362 p3422 p3564 p3917 p4789 p5220 : Prop)
    (h105646 : p4789)
    (h88476 : (¬ p3917) ∨ (¬ p3564) ∨ p3156 ∨ (¬ p4789) ∨ (¬ p3362) ∨ (¬ p5220) ∨ (¬ p2573) ∨ (¬ p2850) ∨ p3146 ∨ p2946)
    (h97817 : p5220 ∨ p3422)
    : p3422 ∨ (¬ p3917) ∨ p2946 ∨ (¬ p2850) ∨ (¬ p2573) ∨ p3156 ∨ (¬ p3564) ∨ (¬ p3362) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4789 := h105646;
    let u10 : (¬ p5220) := (Or.elim h88476 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h97817 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111654 (p2363 p3266 p3461 p4171 : Prop)
    (h79610 : (¬ p4171) ∨ p3266 ∨ (¬ p3461))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3461) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4171) := (Or.elim h79610 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96436 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111655 (p2363 p4171 p4397 p4450 : Prop)
    (h6924 : (¬ p4171) ∨ p4397 ∨ (¬ p4450))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ p4397 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4397) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4171) := (Or.elim h6924 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96436 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111657 (p2088 p2363 p3322 p4170 p4171 : Prop)
    (h6235 : (¬ p2088) ∨ (¬ p3322) ∨ (¬ p4170) ∨ (¬ p4171))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p4170) ∨ (¬ p3322) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4171) := (Or.elim h6235 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h96436 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111660 (p2187 p2363 p3125 p3256 p4171 p4774 : Prop)
    (h75291 : p3125 ∨ (¬ p4171) ∨ (¬ p3256) ∨ (¬ p2187) ∨ (¬ p4774))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p4774) ∨ (¬ p3256) ∨ (¬ p2187) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4171) := (Or.elim h75291 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111661 (p2352 p2363 p3146 p3564 p4134 p4171 : Prop)
    (h105379 : p4134)
    (h78777 : p3564 ∨ (¬ p4171) ∨ (¬ p3146) ∨ (¬ p2352) ∨ (¬ p4134))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ p3564 ∨ (¬ p2352) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4134 := h105379;
    let u5 : (¬ p4171) := (Or.elim h78777 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111663 (p2363 p2528 p2668 p3323 p4171 p4384 : Prop)
    (h106167 : p4384)
    (h79230 : p3323 ∨ (¬ p4171) ∨ (¬ p2528) ∨ (¬ p4384) ∨ (¬ p2668))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ p3323 ∨ (¬ p2668) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4384 := h106167;
    let u5 : (¬ p4171) := (Or.elim h79230 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111664 (p2363 p2668 p3323 p3979 p4171 p5568 : Prop)
    (h79243 : (¬ p5568) ∨ (¬ p2668) ∨ (¬ p3979) ∨ (¬ p4171) ∨ p3323)
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3979) ∨ p3323 ∨ (¬ p2668) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4171) := (Or.elim h79243 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111665 (p2363 p2528 p3063 p3319 p4171 p4384 : Prop)
    (h106167 : p4384)
    (h83538 : p3319 ∨ (¬ p4171) ∨ (¬ p4384) ∨ (¬ p2528) ∨ (¬ p3063))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3063) ∨ p3319 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4384 := h106167;
    let u5 : (¬ p4171) := (Or.elim h83538 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111666 (p2363 p3063 p3146 p3319 p4134 p4171 : Prop)
    (h105379 : p4134)
    (h83539 : p3319 ∨ (¬ p4171) ∨ (¬ p3146) ∨ (¬ p3063) ∨ (¬ p4134))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3063) ∨ p3319 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4134 := h105379;
    let u5 : (¬ p4171) := (Or.elim h83539 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111668 (p2352 p2363 p2459 p3564 p4133 p4171 : Prop)
    (h105712 : p4133)
    (h95241 : p3564 ∨ (¬ p4171) ∨ (¬ p2459) ∨ (¬ p2352) ∨ (¬ p4133))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ p3564 ∨ (¬ p2459) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    let u5 : (¬ p4171) := (Or.elim h95241 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111671 (p2187 p2363 p2459 p3125 p4133 p4171 : Prop)
    (h105712 : p4133)
    (h100333 : p3125 ∨ (¬ p4171) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2187))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p2459) ∨ (¬ p2187) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    let u5 : (¬ p4171) := (Or.elim h100333 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111674 (p2363 p2459 p3276 p3461 p4045 p4171 p4420 : Prop)
    (h105707 : p4420)
    (h79533 : p3276 ∨ (¬ p4171) ∨ (¬ p2459) ∨ (¬ p4045) ∨ (¬ p3461) ∨ (¬ p4420))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3461) ∨ (¬ p4045) ∨ (¬ p2459) ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4420 := h105707;
    let u6 : (¬ p4171) := (Or.elim h79533 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111675 (p2363 p2383 p3073 p3654 p4171 p4370 p4384 : Prop)
    (h106167 : p4384)
    (h80252 : (¬ p3073) ∨ (¬ p4171) ∨ p3654 ∨ (¬ p4370) ∨ (¬ p2383) ∨ (¬ p4384))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3073) ∨ (¬ p2383) ∨ p3654 ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4384 := h106167;
    let u6 : (¬ p4171) := (Or.elim h80252 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111678 (p2363 p2383 p2528 p3654 p3693 p4134 p4171 : Prop)
    (h105379 : p4134)
    (h83101 : p3654 ∨ (¬ p4171) ∨ (¬ p4134) ∨ (¬ p3693) ∨ (¬ p2528) ∨ (¬ p2383))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p2528) ∨ (¬ p3693) ∨ p3654 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4134 := h105379;
    let u6 : (¬ p4171) := (Or.elim h83101 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111683 (p2363 p2383 p3125 p3743 p3979 p4171 p5122 : Prop)
    (h105483 : p5122)
    (h94125 : (¬ p3979) ∨ (¬ p5122) ∨ p3125 ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4171))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3979) ∨ p3125 ∨ (¬ p2383) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5122 := h105483;
    let u6 : (¬ p4171) := (Or.elim h94125 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111684 (p2363 p2383 p2779 p3917 p3979 p4171 p5122 : Prop)
    (h105483 : p5122)
    (h41866 : (¬ p2383) ∨ (¬ p2779) ∨ (¬ p3917) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p3979) ∨ (¬ p3917) ∨ (¬ p2383) ∨ (¬ p2779) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5122 := h105483;
    let u6 : (¬ p4171) := (Or.elim h41866 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111685 (p2363 p2459 p2668 p3917 p4133 p4171 p4328 : Prop)
    (h105712 : p4133)
    (h42018 : (¬ p2459) ∨ (¬ p2668) ∨ (¬ p3917) ∨ (¬ p4133) ∨ (¬ p4171) ∨ (¬ p4328))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ (¬ p4328) ∨ (¬ p2668) ∨ (¬ p3917) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4171) := (Or.elim h42018 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111686 (p2187 p2363 p2459 p3323 p3986 p4133 p4171 : Prop)
    (h105712 : p4133)
    (h101687 : p3323 ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3986) ∨ (¬ p4133) ∨ (¬ p4171))
    (h96436 : p4171 ∨ p2363)
    : p2363 ∨ p3323 ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4171) := (Or.elim h101687 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h96436 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111692 (p2417 p2761 p3276 p4451 : Prop)
    (h79545 : p3276 ∨ (¬ p4451) ∨ (¬ p2761))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3276 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4451) := (Or.elim h79545 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96424 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111696 (p2417 p2911 p2922 p3193 p4451 p4668 : Prop)
    (h105414 : p4668)
    (h81641 : p3193 ∨ (¬ p4451) ∨ p2911 ∨ (¬ p4668) ∨ p2922)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3193 ∨ p2922 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4451) := (Or.elim h81641 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111697 (p2417 p2437 p2761 p2922 p3193 p4451 : Prop)
    (h81651 : p3193 ∨ p2922 ∨ (¬ p2437) ∨ (¬ p2761) ∨ (¬ p4451))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p2922 ∨ p3193 ∨ (¬ p2761) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4451) := (Or.elim h81651 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111699 (p2417 p2922 p3193 p3246 p4451 p4647 : Prop)
    (h105412 : p4647)
    (h81656 : p3193 ∨ (¬ p4451) ∨ p2922 ∨ (¬ p4647) ∨ p3246)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3193 ∨ p3246 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    let u5 : (¬ p4451) := (Or.elim h81656 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111700 (p2396 p2417 p2922 p3193 p4451 p4712 : Prop)
    (h105422 : p4712)
    (h81657 : p3193 ∨ (¬ p4451) ∨ p2396 ∨ p2922 ∨ (¬ p4712))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3193 ∨ p2922 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4712 := h105422;
    let u5 : (¬ p4451) := (Or.elim h81657 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111701 (p2417 p2449 p3355 p3389 p4327 p4451 : Prop)
    (h105381 : p4327)
    (h85011 : (¬ p3355) ∨ (¬ p4451) ∨ p3389 ∨ p2449 ∨ (¬ p4327))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3389 ∨ p2449 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4327 := h105381;
    let u5 : (¬ p4451) := (Or.elim h85011 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111702 (p2417 p3246 p3355 p3389 p4451 p4647 : Prop)
    (h105412 : p4647)
    (h85012 : (¬ p3355) ∨ (¬ p4451) ∨ p3246 ∨ (¬ p4647) ∨ p3389)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3246 ∨ p3389 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    let u5 : (¬ p4451) := (Or.elim h85012 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111703 (p2417 p2437 p2761 p3355 p3389 p4451 : Prop)
    (h85026 : (¬ p2437) ∨ (¬ p3355) ∨ p3389 ∨ (¬ p2761) ∨ (¬ p4451))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3389 ∨ (¬ p2437) ∨ (¬ p3355) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4451) := (Or.elim h85026 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111704 (p2417 p2930 p3355 p3389 p3631 p4451 : Prop)
    (h105376 : p2930)
    (h85042 : (¬ p3355) ∨ (¬ p4451) ∨ p3631 ∨ p3389 ∨ (¬ p2930))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3631 ∨ p3389 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2930 := h105376;
    let u5 : (¬ p4451) := (Or.elim h85042 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111705 (p2417 p2761 p2922 p3355 p3389 p4451 : Prop)
    (h85047 : (¬ p4451) ∨ (¬ p2922) ∨ p3389 ∨ (¬ p2761) ∨ (¬ p3355))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2761) ∨ (¬ p3355) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4451) := (Or.elim h85047 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111708 (p2396 p2417 p3201 p3333 p4451 p4712 : Prop)
    (h105422 : p4712)
    (h95623 : (¬ p4451) ∨ (¬ p3333) ∨ p2396 ∨ (¬ p4712) ∨ p3201)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p2396 ∨ (¬ p3333) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4712 := h105422;
    let u5 : (¬ p4451) := (Or.elim h95623 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111709 (p2177 p2417 p2449 p2911 p3192 p4451 : Prop)
    (h100129 : p2449 ∨ (¬ p3192) ∨ (¬ p2177) ∨ (¬ p4451) ∨ p2911)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ (¬ p3192) ∨ (¬ p2177) ∨ p2911 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4451) := (Or.elim h100129 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111710 (p2417 p2437 p2930 p3343 p3631 p4451 : Prop)
    (h105376 : p2930)
    (h101965 : (¬ p3343) ∨ (¬ p4451) ∨ p3631 ∨ p2437 ∨ (¬ p2930))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3631 ∨ p2437 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2930 := h105376;
    let u5 : (¬ p4451) := (Or.elim h101965 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111711 (p2396 p2417 p2449 p3276 p3506 p4451 : Prop)
    (h110274 : (¬ p2449) ∨ p3276 ∨ (¬ p4451) ∨ (¬ p3506) ∨ p2396)
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ (¬ p2449) ∨ p3276 ∨ (¬ p3506) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4451) := (Or.elim h110274 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111726 (p2098 p2363 p2417 p2922 p3193 p3389 p3609 p3657 p4079 p4451 p4503 p4736 : Prop)
    (h105431 : p4736)
    (h106530 : p4503)
    (h81672 : (¬ p3389) ∨ p3193 ∨ (¬ p4079) ∨ p3609 ∨ (¬ p4451) ∨ p2922 ∨ (¬ p4503) ∨ (¬ p4736) ∨ (¬ p3657) ∨ p2098 ∨ (¬ p2363))
    (h96424 : p4451 ∨ (¬ p2417))
    : (¬ p2417) ∨ p3193 ∨ p3609 ∨ p2922 ∨ (¬ p3389) ∨ (¬ p2363) ∨ p2098 ∨ (¬ p4079) ∨ (¬ p3657) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4736 := h105431;
    let u10 : p4503 := h106530;
    let u11 : (¬ p4451) := (Or.elim h81672 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u6 q9))) (fun r9 => (False.elim (r9 u5))))))))))))))))))))));
    (Or.elim h96424 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111731 (p2122 p2177 p2717 p4471 : Prop)
    (h89184 : (¬ p2717) ∨ (¬ p4471) ∨ p2177)
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ (¬ p2717) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4471) := (Or.elim h89184 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102189 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111732 (p2122 p2396 p3434 p4471 : Prop)
    (h90119 : (¬ p3434) ∨ (¬ p4471) ∨ p2396)
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ (¬ p3434) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4471) := (Or.elim h90119 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102189 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111736 (p2122 p2295 p2707 p2829 p4471 p4843 : Prop)
    (h105449 : p4843)
    (h88275 : (¬ p4471) ∨ (¬ p2295) ∨ (¬ p4843) ∨ p2707 ∨ (¬ p2829))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2707 ∨ (¬ p2295) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4471) := (Or.elim h88275 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111737 (p2122 p2553 p2707 p2829 p4471 p5222 : Prop)
    (h105793 : p5222)
    (h88342 : p2707 ∨ (¬ p2829) ∨ (¬ p2553) ∨ (¬ p4471) ∨ (¬ p5222))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2707 ∨ (¬ p2829) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5222 := h105793;
    let u5 : (¬ p4471) := (Or.elim h88342 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111738 (p2122 p2707 p2819 p2829 p4405 p4471 : Prop)
    (h105512 : p4405)
    (h88375 : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p4471) ∨ p2707 ∨ (¬ p4405))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2707 ∨ (¬ p2819) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4471) := (Or.elim h88375 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111739 (p2122 p2707 p2829 p3483 p4471 p4624 : Prop)
    (h105408 : p4624)
    (h88441 : (¬ p3483) ∨ p2707 ∨ (¬ p4624) ∨ (¬ p2829) ∨ (¬ p4471))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2707 ∨ (¬ p3483) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4471) := (Or.elim h88441 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111740 (p2122 p2274 p2774 p3425 p4471 p4889 : Prop)
    (h45010 : (¬ p2274) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4889))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ (¬ p2774) ∨ (¬ p2274) ∨ (¬ p3425) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4471) := (Or.elim h45010 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111741 (p2122 p2553 p2598 p3367 p3425 p4471 : Prop)
    (h88663 : (¬ p2553) ∨ (¬ p4471) ∨ (¬ p2598) ∨ p3367 ∨ (¬ p3425))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p3367 ∨ (¬ p3425) ∨ (¬ p2598) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4471) := (Or.elim h88663 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111743 (p2122 p2295 p2774 p3425 p4471 p4843 : Prop)
    (h105449 : p4843)
    (h52881 : (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4843))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ (¬ p3425) ∨ (¬ p2295) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4471) := (Or.elim h52881 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111744 (p2122 p2396 p2774 p2829 p3425 p4471 : Prop)
    (h90124 : (¬ p3425) ∨ p2829 ∨ (¬ p4471) ∨ (¬ p2774) ∨ p2396)
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2396 ∨ p2829 ∨ (¬ p2774) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4471) := (Or.elim h90124 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111745 (p2122 p2553 p2774 p3425 p4471 p5222 : Prop)
    (h105793 : p5222)
    (h53616 : (¬ p2553) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p5222))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ (¬ p3425) ∨ (¬ p2774) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5222 := h105793;
    let u5 : (¬ p4471) := (Or.elim h53616 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111754 (p2122 p2274 p2707 p2829 p3958 p4390 p4471 : Prop)
    (h105378 : p3958)
    (h88277 : p2707 ∨ (¬ p2829) ∨ (¬ p3958) ∨ (¬ p2274) ∨ (¬ p4390) ∨ (¬ p4471))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2707 ∨ (¬ p4390) ∨ (¬ p2829) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    let u6 : (¬ p4471) := (Or.elim h88277 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111759 (p2122 p2177 p2707 p2774 p2829 p3873 p4471 : Prop)
    (h101362 : p2707 ∨ (¬ p2829) ∨ p2774 ∨ (¬ p3873) ∨ p2177 ∨ (¬ p4471))
    (h102189 : p4471 ∨ p2122)
    : p2122 ∨ p2177 ∨ p2774 ∨ (¬ p2829) ∨ p2707 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4471) := (Or.elim h101362 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => r4))))))))));
    (Or.elim h102189 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111772 (p2098 p2717 p3425 p3685 : Prop)
    (h17796 : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3685))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p2098) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3685) := (Or.elim h17796 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h97921 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111773 (p2707 p2717 p3537 p3685 : Prop)
    (h89777 : (¬ p3537) ∨ p2707 ∨ (¬ p3685))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p3537) ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3685) := (Or.elim h89777 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h97921 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111774 (p2717 p3685 p4782 p4968 : Prop)
    (h38910 : (¬ p3685) ∨ (¬ p4782) ∨ p4968)
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p4968 ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4968) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3685) := (Or.elim h38910 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h97921 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111775 (p2717 p3685 p4357 p4364 : Prop)
    (h40253 : (¬ p3685) ∨ (¬ p4357) ∨ p4364)
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p4364 ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4364) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3685) := (Or.elim h40253 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h97921 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111781 (p2459 p2717 p2881 p3609 p3685 p4895 : Prop)
    (h97108 : p3609 ∨ (¬ p3685) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p4895))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p2459) ∨ (¬ p2881) ∨ p3609 ∨ (¬ p4895) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3685) := (Or.elim h97108 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111782 (p2088 p2110 p2696 p2717 p3609 p3685 p4782 : Prop)
    (h82696 : (¬ p2110) ∨ p2696 ∨ (¬ p2088) ∨ (¬ p3685) ∨ p3609 ∨ (¬ p4782))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p2110) ∨ (¬ p2088) ∨ p3609 ∨ p2696 ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3685) := (Or.elim h82696 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111784 (p2088 p2717 p3425 p3609 p3685 p3873 p5239 : Prop)
    (h88657 : p3609 ∨ (¬ p3873) ∨ (¬ p3425) ∨ (¬ p5239) ∨ (¬ p2088) ∨ (¬ p3685))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p2088) ∨ p3609 ∨ (¬ p3873) ∨ (¬ p3425) ∨ (¬ p5239) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5239 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3685) := (Or.elim h88657 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111785 (p2098 p2598 p2717 p2922 p3658 p3685 p5214 : Prop)
    (h105492 : p5214)
    (h89802 : (¬ p3658) ∨ (¬ p2098) ∨ p2598 ∨ (¬ p5214) ∨ (¬ p3685) ∨ p2922)
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p2922 ∨ (¬ p2098) ∨ p2598 ∨ (¬ p3658) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5214 := h105492;
    let u6 : (¬ p3685) := (Or.elim h89802 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111792 (p2459 p2696 p2717 p3005 p3256 p3425 p3685 : Prop)
    (h110581 : p3005 ∨ p3256 ∨ (¬ p2696) ∨ (¬ p3685) ∨ (¬ p3425) ∨ (¬ p2459))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p3005 ∨ p3256 ∨ (¬ p2696) ∨ (¬ p3425) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3685) := (Or.elim h110581 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111797 (p2363 p2717 p3577 p3609 p3685 p4063 p4138 p5564 : Prop)
    (h89800 : (¬ p4063) ∨ (¬ p3577) ∨ (¬ p4138) ∨ (¬ p5564) ∨ p3609 ∨ (¬ p2363) ∨ (¬ p3685))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p5564) ∨ (¬ p3577) ∨ (¬ p4138) ∨ (¬ p4063) ∨ (¬ p2363) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3685) := (Or.elim h89800 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => r5))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111799 (p2449 p2717 p2881 p3685 p3941 p4275 p4325 p5612 : Prop)
    (h59365 : (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3685) ∨ (¬ p3941) ∨ (¬ p4275) ∨ (¬ p4325) ∨ (¬ p5612))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p4325) ∨ (¬ p5612) ∨ (¬ p3941) ∨ (¬ p4275) ∨ (¬ p2449) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3685) := (Or.elim h59365 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111802 (p2187 p2284 p2459 p2717 p2946 p3425 p3609 p3685 p4133 p4786 : Prop)
    (h105712 : p4133)
    (h106425 : p4786)
    (h89803 : p3609 ∨ (¬ p2946) ∨ (¬ p4786) ∨ (¬ p3685) ∨ (¬ p2459) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p3425))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p3425) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2946) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    let u8 : p4786 := h106425;
    let u9 : (¬ p3685) := (Or.elim h89803 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111803 (p2373 p2406 p2459 p2717 p3379 p3425 p3609 p3685 p4736 p4902 : Prop)
    (h105431 : p4736)
    (h105456 : p4902)
    (h97157 : (¬ p2373) ∨ (¬ p3685) ∨ p3609 ∨ (¬ p3425) ∨ (¬ p4736) ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p2406))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3425) ∨ p3609 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4902 := h105456;
    let u9 : (¬ p3685) := (Or.elim h97157 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111805 (p2166 p2210 p2241 p2459 p2717 p2744 p3366 p3425 p3609 p3685 p4902 : Prop)
    (h106503 : p2744)
    (h105456 : p4902)
    (h89801 : (¬ p3685) ∨ (¬ p2166) ∨ p3609 ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p4902) ∨ (¬ p3425) ∨ p2241)
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p3609 ∨ p2241 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p2459) ∨ (¬ p3366) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4902 := h105456;
    let u10 : (¬ p3685) := (Or.elim h89801 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111808 (p2441 p2717 p3146 p3193 p3276 p3347 p3422 p3609 p3685 p3759 p4253 p4715 p5503 : Prop)
    (h105423 : p4715)
    (h97202 : (¬ p5503) ∨ p3609 ∨ (¬ p3146) ∨ (¬ p2441) ∨ p3193 ∨ (¬ p3759) ∨ (¬ p3685) ∨ (¬ p4253) ∨ p3422 ∨ (¬ p3276) ∨ (¬ p4715) ∨ (¬ p3347))
    (h97921 : p3685 ∨ p2717)
    : p2717 ∨ p3193 ∨ (¬ p3276) ∨ p3422 ∨ (¬ p3146) ∨ p3609 ∨ (¬ p3759) ∨ (¬ p3347) ∨ (¬ p2441) ∨ (¬ p5503) ∨ (¬ p4253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4715 := h105423;
    let u12 : (¬ p3685) := (Or.elim h97202 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u7))))))))))))))))))))))));
    (Or.elim h97921 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111812 (p2122 p2707 p2829 p3689 : Prop)
    (h87984 : p2829 ∨ (¬ p2707) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p2707) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3689) := (Or.elim h87984 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h101823 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111815 (p2122 p2774 p3689 p3819 p3959 : Prop)
    (h87985 : p2774 ∨ (¬ p3689) ∨ (¬ p3959) ∨ (¬ p3819))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p3959) ∨ (¬ p3819) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3689) := (Or.elim h87985 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111816 (p2122 p2177 p2598 p2717 p2774 p3689 : Prop)
    (h86307 : p2717 ∨ p2774 ∨ (¬ p2177) ∨ (¬ p3689) ∨ (¬ p2598))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2598) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3689) := (Or.elim h86307 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111817 (p2122 p2177 p2307 p2717 p2788 p3689 : Prop)
    (h105375 : p2788)
    (h87973 : (¬ p2307) ∨ p2717 ∨ (¬ p3689) ∨ (¬ p2177) ∨ (¬ p2788))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p2717 ∨ (¬ p2307) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2788 := h105375;
    let u5 : (¬ p3689) := (Or.elim h87973 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111818 (p2122 p2177 p2717 p3483 p3689 p4624 : Prop)
    (h105408 : p4624)
    (h87975 : (¬ p3483) ∨ (¬ p3689) ∨ p2717 ∨ (¬ p2177) ∨ (¬ p4624))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p2717 ∨ (¬ p2177) ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p3689) := (Or.elim h87975 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111819 (p2122 p2177 p2553 p2717 p3689 p5222 : Prop)
    (h105793 : p5222)
    (h87976 : (¬ p2553) ∨ p2717 ∨ (¬ p2177) ∨ (¬ p5222) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5222 := h105793;
    let u5 : (¬ p3689) := (Or.elim h87976 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111820 (p2122 p2396 p2819 p3434 p3689 p4405 : Prop)
    (h105512 : p4405)
    (h87982 : (¬ p2819) ∨ p3434 ∨ (¬ p2396) ∨ (¬ p4405) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p3434 ∨ (¬ p2396) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p3689) := (Or.elim h87982 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111821 (p2122 p2295 p2396 p3434 p3689 p4843 : Prop)
    (h105449 : p4843)
    (h87989 : (¬ p2295) ∨ (¬ p2396) ∨ p3434 ∨ (¬ p4843) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p3434 ∨ (¬ p2396) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p3689) := (Or.elim h87989 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111824 (p2122 p2829 p3367 p3389 p3689 p4106 p4730 : Prop)
    (h106074 : p4730)
    (h77781 : (¬ p4106) ∨ (¬ p3689) ∨ (¬ p3389) ∨ (¬ p4730) ∨ p2829 ∨ (¬ p3367))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p4106) ∨ p2829 ∨ (¬ p3367) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4730 := h106074;
    let u6 : (¬ p3689) := (Or.elim h77781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111825 (p2122 p2396 p2417 p2598 p2774 p3689 p4106 : Prop)
    (h86357 : p2774 ∨ p2417 ∨ (¬ p4106) ∨ (¬ p3689) ∨ (¬ p2598) ∨ (¬ p2396))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p2598) ∨ p2417 ∨ (¬ p2396) ∨ (¬ p4106) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3689) := (Or.elim h86357 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111827 (p2122 p2312 p2553 p3434 p3516 p3689 p5222 : Prop)
    (h105793 : p5222)
    (h87974 : (¬ p2312) ∨ (¬ p3516) ∨ p3434 ∨ (¬ p2553) ∨ (¬ p5222) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ p3434 ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5222 := h105793;
    let u6 : (¬ p3689) := (Or.elim h87974 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111835 (p2122 p2187 p3689 p4075 p4185 p4405 p4423 p4427 : Prop)
    (h105512 : p4405)
    (h42248 : (¬ p2187) ∨ (¬ p3689) ∨ (¬ p4075) ∨ (¬ p4185) ∨ (¬ p4405) ∨ (¬ p4423) ∨ (¬ p4427))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p4423) ∨ (¬ p2187) ∨ (¬ p4185) ∨ (¬ p4427) ∨ (¬ p4075) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p3689) := (Or.elim h42248 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111839 (p2122 p2274 p2312 p2717 p3527 p3546 p3689 p4889 : Prop)
    (h87991 : (¬ p3527) ∨ (¬ p2274) ∨ (¬ p3546) ∨ p2717 ∨ (¬ p2312) ∨ (¬ p4889) ∨ (¬ p3689))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p3527) ∨ (¬ p3546) ∨ p2717 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3689) := (Or.elim h87991 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111848 (p2122 p2166 p2210 p2717 p2774 p3146 p3689 p4736 p5118 p5558 : Prop)
    (h105431 : p4736)
    (h105482 : p5118)
    (h87981 : (¬ p5558) ∨ (¬ p3689) ∨ p2717 ∨ (¬ p5118) ∨ (¬ p2210) ∨ (¬ p4736) ∨ p2774 ∨ (¬ p3146) ∨ (¬ p2166))
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p5558) ∨ (¬ p3146) ∨ p2774 ∨ p2717 ∨ (¬ p2166) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p5118 := h105482;
    let u9 : (¬ p3689) := (Or.elim h87981 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111849 (p2122 p2331 p2470 p2528 p2630 p2656 p2717 p3689 p4328 p5118 p5558 : Prop)
    (h105482 : p5118)
    (h101087 : (¬ p5558) ∨ (¬ p5118) ∨ (¬ p4328) ∨ p2331 ∨ (¬ p2656) ∨ (¬ p3689) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ p2717)
    (h101823 : p3689 ∨ p2122)
    : p2122 ∨ (¬ p4328) ∨ (¬ p5558) ∨ (¬ p2528) ∨ (¬ p2470) ∨ p2717 ∨ (¬ p2656) ∨ (¬ p2630) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5118 := h105482;
    let u10 : (¬ p3689) := (Or.elim h101087 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u5 r8))))))))))))))))))));
    (Or.elim h101823 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111852 (p2619 p3146 p3609 p4188 : Prop)
    (h88204 : p3609 ∨ (¬ p3146) ∨ (¬ p4188))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p3609 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4188) := (Or.elim h88204 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h101917 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111857 (p2098 p2132 p2619 p2839 p3146 p4188 : Prop)
    (h83700 : (¬ p4188) ∨ (¬ p2098) ∨ (¬ p3146) ∨ p2132 ∨ (¬ p2839))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p2839) ∨ (¬ p2098) ∨ (¬ p3146) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4188) := (Or.elim h83700 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111858 (p2098 p2132 p2373 p2619 p4188 p4885 : Prop)
    (h88201 : (¬ p4188) ∨ (¬ p2098) ∨ p2373 ∨ p2132 ∨ (¬ p4885))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p2098) ∨ p2373 ∨ (¬ p4885) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4188) := (Or.elim h88201 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111859 (p2098 p2132 p2166 p2619 p4188 p4875 : Prop)
    (h106227 : p4875)
    (h88208 : (¬ p2098) ∨ (¬ p4188) ∨ p2132 ∨ p2166 ∨ (¬ p4875))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p2166 ∨ (¬ p2098) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4875 := h106227;
    let u5 : (¬ p4188) := (Or.elim h88208 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111861 (p2619 p2839 p2860 p3537 p4188 p4509 : Prop)
    (h105392 : p4509)
    (h88211 : (¬ p3537) ∨ (¬ p4188) ∨ p2860 ∨ (¬ p4509) ∨ p2839)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p3537) ∨ p2860 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    let u5 : (¬ p4188) := (Or.elim h88211 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111862 (p2132 p2619 p2839 p3146 p3537 p4188 : Prop)
    (h89745 : (¬ p3537) ∨ (¬ p4188) ∨ p2839 ∨ (¬ p3146) ∨ (¬ p2132))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p3537) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4188) := (Or.elim h89745 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111863 (p2373 p2619 p2839 p3537 p4188 p4885 : Prop)
    (h89746 : (¬ p3537) ∨ (¬ p4188) ∨ (¬ p4885) ∨ p2839 ∨ p2373)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p2373 ∨ (¬ p3537) ∨ p2839 ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4188) := (Or.elim h89746 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111867 (p2098 p2132 p2619 p3105 p3146 p4188 : Prop)
    (h107815 : p3146 ∨ (¬ p2098) ∨ p3105 ∨ (¬ p4188) ∨ p2132)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p3146 ∨ (¬ p2098) ∨ p3105 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4188) := (Or.elim h107815 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111868 (p2284 p2619 p4009 p4188 p4237 p4509 p5612 : Prop)
    (h105392 : p4509)
    (h84958 : (¬ p5612) ∨ (¬ p4009) ∨ (¬ p4509) ∨ (¬ p4188) ∨ p2284 ∨ (¬ p4237))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p4009) ∨ (¬ p5612) ∨ (¬ p4237) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    let u6 : (¬ p4188) := (Or.elim h84958 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111869 (p2098 p2553 p2619 p2774 p3156 p4188 p4342 : Prop)
    (h86336 : (¬ p2098) ∨ (¬ p4188) ∨ p2774 ∨ (¬ p4342) ∨ p2553 ∨ p3156)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p2098) ∨ p2553 ∨ (¬ p4342) ∨ p3156 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4188) := (Or.elim h86336 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111872 (p2098 p2132 p2284 p2619 p4188 p4316 p4509 : Prop)
    (h105392 : p4509)
    (h88203 : (¬ p2098) ∨ (¬ p4188) ∨ p2132 ∨ (¬ p4316) ∨ p2284 ∨ (¬ p4509))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p2098) ∨ p2284 ∨ p2132 ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    let u6 : (¬ p4188) := (Or.elim h88203 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111880 (p2459 p2608 p2619 p2911 p3389 p3537 p3969 p4188 p5122 p5193 : Prop)
    (h105488 : p5193)
    (h105483 : p5122)
    (h89775 : (¬ p3969) ∨ (¬ p2608) ∨ (¬ p5122) ∨ p3389 ∨ p2459 ∨ p2911 ∨ (¬ p4188) ∨ (¬ p3537) ∨ (¬ p5193))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p3537) ∨ p2459 ∨ p2911 ∨ p3389 ∨ (¬ p3969) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p5122 := h105483;
    let u9 : (¬ p4188) := (Or.elim h89775 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111881 (p2254 p2331 p2363 p2608 p2619 p2668 p3537 p3969 p4188 p5122 : Prop)
    (h105366 : p2254)
    (h105483 : p5122)
    (h89784 : (¬ p3537) ∨ (¬ p3969) ∨ (¬ p2254) ∨ p2668 ∨ (¬ p4188) ∨ p2331 ∨ (¬ p5122) ∨ (¬ p2608) ∨ p2363)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p2668 ∨ p2363 ∨ (¬ p2608) ∨ p2331 ∨ (¬ p3537) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p5122 := h105483;
    let u9 : (¬ p4188) := (Or.elim h89784 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111882 (p2254 p2331 p2608 p2619 p3323 p3461 p3537 p3969 p4188 p5119 : Prop)
    (h105366 : p2254)
    (h89786 : (¬ p3969) ∨ (¬ p4188) ∨ p2331 ∨ p3461 ∨ (¬ p3537) ∨ (¬ p5119) ∨ (¬ p2254) ∨ (¬ p2608) ∨ p3323)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p3323 ∨ p3461 ∨ (¬ p2608) ∨ p2331 ∨ (¬ p3537) ∨ (¬ p3969) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    let u9 : (¬ p4188) := (Or.elim h89786 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (u1 r7))))))))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111888 (p2098 p2132 p2252 p2619 p2655 p2748 p2911 p3146 p3389 p4188 p5118 p5558 : Prop)
    (h105482 : p5118)
    (h89425 : (¬ p2098) ∨ p2132 ∨ (¬ p5558) ∨ (¬ p5118) ∨ (¬ p4188) ∨ (¬ p3146) ∨ (¬ p2252) ∨ p2911 ∨ (¬ p2748) ∨ (¬ p2655) ∨ p3389)
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ p3389 ∨ (¬ p3146) ∨ p2911 ∨ (¬ p2098) ∨ (¬ p2655) ∨ (¬ p5558) ∨ p2132 ∨ (¬ p2252) ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5118 := h105482;
    let u11 : (¬ p4188) := (Or.elim h89425 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (u1 r9))))))))))))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111889 (p2136 p2220 p2295 p2573 p2619 p3266 p3609 p3791 p4188 p4389 p4419 p4826 : Prop)
    (h105444 : p4826)
    (h97159 : (¬ p3791) ∨ p3266 ∨ (¬ p2295) ∨ p3609 ∨ (¬ p4188) ∨ (¬ p2573) ∨ (¬ p4826) ∨ (¬ p4419) ∨ (¬ p2136) ∨ p2220 ∨ (¬ p4389))
    (h101917 : p4188 ∨ (¬ p2619))
    : (¬ p2619) ∨ (¬ p3791) ∨ (¬ p4389) ∨ p3266 ∨ p2220 ∨ p3609 ∨ (¬ p2295) ∨ (¬ p2573) ∨ (¬ p2136) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4826 := h105444;
    let u11 : (¬ p4188) := (Or.elim h97159 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u4 q9))) (fun r9 => (False.elim (r9 u2))))))))))))))))))))));
    (Or.elim h101917 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111892 (p2363 p3266 p3461 p4345 : Prop)
    (h38851 : (¬ p3266) ∨ p3461 ∨ (¬ p4345))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ p3461 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4345) := (Or.elim h38851 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h99552 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111893 (p2363 p2532 p4345 p5045 : Prop)
    (h33471 : p2532 ∨ (¬ p4345) ∨ (¬ p5045))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ p2532 ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2532) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4345) := (Or.elim h33471 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h99552 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111894 (p2363 p2528 p3990 p4157 p4345 : Prop)
    (h80733 : (¬ p4157) ∨ p2528 ∨ (¬ p3990) ∨ (¬ p4345))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p4157) ∨ p2528 ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4345) := (Or.elim h80733 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h99552 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111896 (p2363 p2528 p2668 p3323 p4345 p4596 : Prop)
    (h80730 : (¬ p3323) ∨ p2528 ∨ (¬ p4345) ∨ (¬ p4596) ∨ p2668)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ p2528 ∨ (¬ p3323) ∨ (¬ p4596) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4345) := (Or.elim h80730 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111897 (p2352 p2363 p2459 p3564 p4345 p4503 : Prop)
    (h106530 : p4503)
    (h80734 : (¬ p3564) ∨ (¬ p4503) ∨ p2459 ∨ (¬ p4345) ∨ p2352)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3564) ∨ p2352 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    let u5 : (¬ p4345) := (Or.elim h80734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111899 (p2352 p2363 p3564 p4345 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h80736 : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p3564) ∨ p2352 ∨ (¬ p4345))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3564) ∨ (¬ p5580) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    let u5 : (¬ p4345) := (Or.elim h80736 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111903 (p2363 p2668 p3323 p4345 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h80747 : (¬ p5580) ∨ (¬ p5118) ∨ p2668 ∨ (¬ p3323) ∨ (¬ p4345))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p5580) ∨ (¬ p3323) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    let u5 : (¬ p4345) := (Or.elim h80747 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111904 (p2363 p2459 p3319 p3923 p4345 p4503 : Prop)
    (h106530 : p4503)
    (h84201 : (¬ p3319) ∨ (¬ p4503) ∨ (¬ p4345) ∨ (¬ p3923) ∨ p2459)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3319) ∨ p2459 ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    let u5 : (¬ p4345) := (Or.elim h84201 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111905 (p2363 p2819 p3483 p4345 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h90234 : (¬ p5580) ∨ (¬ p3483) ∨ (¬ p4345) ∨ p2819 ∨ (¬ p5118))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p5580) ∨ (¬ p3483) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    let u5 : (¬ p4345) := (Or.elim h90234 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111906 (p2363 p2383 p2459 p3654 p4345 p4503 : Prop)
    (h106530 : p4503)
    (h90927 : (¬ p3654) ∨ (¬ p4503) ∨ (¬ p4345) ∨ p2383 ∨ p2459)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3654) ∨ p2459 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    let u5 : (¬ p4345) := (Or.elim h90927 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111907 (p2363 p2383 p3146 p3654 p4345 p4433 : Prop)
    (h106150 : p4433)
    (h90929 : (¬ p3654) ∨ p3146 ∨ (¬ p4433) ∨ (¬ p4345) ∨ p2383)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3654) ∨ p3146 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4433 := h106150;
    let u5 : (¬ p4345) := (Or.elim h90929 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111910 (p2363 p2459 p2668 p3323 p4345 p4503 : Prop)
    (h106530 : p4503)
    (h91755 : (¬ p3323) ∨ (¬ p4503) ∨ p2459 ∨ (¬ p4345) ∨ p2668)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ p2668 ∨ p2459 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    let u5 : (¬ p4345) := (Or.elim h91755 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111912 (p2088 p2352 p2363 p2383 p3564 p4345 : Prop)
    (h108945 : p2383 ∨ (¬ p3564) ∨ p2352 ∨ (¬ p4345) ∨ p2088)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ p2383 ∨ (¬ p3564) ∨ p2352 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4345) := (Or.elim h108945 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111915 (p2363 p2668 p3125 p3986 p4345 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h79480 : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p4345) ∨ p2668 ∨ (¬ p3986) ∨ (¬ p3125))
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p5580) ∨ (¬ p3125) ∨ p2668 ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5118 := h105482;
    let u6 : (¬ p4345) := (Or.elim h79480 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111920 (p2088 p2363 p2819 p3483 p3858 p4345 p4995 : Prop)
    (h90242 : (¬ p3483) ∨ p2088 ∨ (¬ p3858) ∨ (¬ p4995) ∨ (¬ p4345) ∨ p2819)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3483) ∨ (¬ p4995) ∨ (¬ p3858) ∨ p2088 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4345) := (Or.elim h90242 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111921 (p2363 p2383 p2386 p3564 p4345 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h91302 : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p3564) ∨ (¬ p2386) ∨ (¬ p4345) ∨ p2383)
    (h99552 : p4345 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3564) ∨ (¬ p5580) ∨ p2383 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5118 := h105482;
    let u6 : (¬ p4345) := (Or.elim h91302 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h99552 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111934 (p2641 p3323 p3848 p4421 : Prop)
    (h33862 : (¬ p2641) ∨ (¬ p3848) ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3848) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4421) := (Or.elim h33862 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h95302 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111935 (p2667 p3286 p3323 p3987 p4421 : Prop)
    (h84987 : p3286 ∨ (¬ p4421) ∨ (¬ p2667) ∨ (¬ p3987))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3286 ∨ (¬ p3987) ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4421) := (Or.elim h84987 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111936 (p2331 p2651 p3323 p3343 p4421 : Prop)
    (h109939 : p3343 ∨ (¬ p4421) ∨ (¬ p2331) ∨ p2651)
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3343 ∨ (¬ p2331) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4421) := (Or.elim h109939 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111937 (p2331 p3166 p3256 p3323 p4421 : Prop)
    (h111094 : p3256 ∨ p3166 ∨ (¬ p2331) ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3256 ∨ p3166 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4421) := (Or.elim h111094 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h95302 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111941 (p2295 p3323 p3461 p3506 p4421 p4624 : Prop)
    (h105408 : p4624)
    (h98648 : (¬ p3506) ∨ p3461 ∨ p2295 ∨ (¬ p4421) ∨ (¬ p4624))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p2295 ∨ p3461 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4421) := (Or.elim h98648 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111942 (p2668 p3323 p3325 p3461 p3506 p3564 p4421 : Prop)
    (h82506 : (¬ p3506) ∨ p3461 ∨ p2668 ∨ p3564 ∨ (¬ p4421) ∨ (¬ p3325))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p2668 ∨ (¬ p3325) ∨ p3564 ∨ p3461 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4421) := (Or.elim h82506 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111945 (p3323 p3461 p3564 p3670 p4421 p4976 p5454 : Prop)
    (h105465 : p4976)
    (h96196 : (¬ p3670) ∨ p3461 ∨ (¬ p5454) ∨ (¬ p4976) ∨ p3564 ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3461 ∨ (¬ p5454) ∨ (¬ p3670) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4976 := h105465;
    let u6 : (¬ p4421) := (Or.elim h96196 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111947 (p2331 p2651 p3276 p3323 p3343 p3461 p4421 : Prop)
    (h111270 : (¬ p3343) ∨ (¬ p4421) ∨ (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p2331))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3343) ∨ (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4421) := (Or.elim h111270 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111949 (p2132 p2331 p2619 p3266 p3323 p3506 p4421 p5568 : Prop)
    (h108990 : p3266 ∨ (¬ p5568) ∨ (¬ p3506) ∨ p2132 ∨ (¬ p2331) ∨ p2619 ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3266 ∨ (¬ p5568) ∨ (¬ p3506) ∨ p2132 ∨ (¬ p2331) ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4421) := (Or.elim h108990 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => r5))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111950 (p2331 p2717 p3266 p3323 p3425 p3506 p4421 p5558 : Prop)
    (h108991 : p3266 ∨ (¬ p5558) ∨ (¬ p3506) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3266 ∨ (¬ p5558) ∨ (¬ p3506) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4421) := (Or.elim h108991 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111955 (p2132 p2331 p2619 p3266 p3323 p3461 p3506 p4421 p5568 : Prop)
    (h109255 : (¬ p3266) ∨ (¬ p4421) ∨ (¬ p2331) ∨ p3461 ∨ p2619 ∨ (¬ p3506) ∨ (¬ p5568) ∨ p2132)
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3266) ∨ (¬ p2331) ∨ p3461 ∨ p2619 ∨ (¬ p3506) ∨ (¬ p5568) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4421) := (Or.elim h109255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111956 (p2331 p2717 p3266 p3323 p3425 p3461 p3506 p4421 p5558 : Prop)
    (h109256 : (¬ p3266) ∨ p3461 ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p5558) ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3266) ∨ p3461 ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4421) := (Or.elim h109256 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => r6))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111957 (p2132 p2331 p2870 p3246 p3323 p3461 p3506 p4421 p4621 p4786 : Prop)
    (h106425 : p4786)
    (h105407 : p4621)
    (h86784 : (¬ p3506) ∨ p3461 ∨ p3246 ∨ (¬ p4786) ∨ (¬ p4421) ∨ (¬ p4621) ∨ p2870 ∨ p2132 ∨ (¬ p2331))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p2331) ∨ p3461 ∨ (¬ p3506) ∨ p3246 ∨ p2132 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : p4621 := h105407;
    let u9 : (¬ p4421) := (Or.elim h86784 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111961 (p2166 p2210 p2248 p2331 p3246 p3323 p3461 p3506 p3747 p4421 p4621 : Prop)
    (h105365 : p2248)
    (h105407 : p4621)
    (h75493 : (¬ p3506) ∨ p3461 ∨ p2166 ∨ p2210 ∨ (¬ p2331) ∨ (¬ p4421) ∨ p3246 ∨ (¬ p4621) ∨ (¬ p2248) ∨ (¬ p3747))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3246 ∨ p2210 ∨ (¬ p2331) ∨ (¬ p3506) ∨ p3461 ∨ p2166 ∨ (¬ p3747) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    let u9 : p4621 := h105407;
    let u10 : (¬ p4421) := (Or.elim h75493 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111962 (p2249 p2509 p2528 p2641 p2651 p3323 p3461 p3487 p3506 p4330 p4421 : Prop)
    (h106513 : p2249)
    (h106329 : p4330)
    (h98162 : p3461 ∨ (¬ p4421) ∨ (¬ p2509) ∨ (¬ p2249) ∨ (¬ p4330) ∨ (¬ p2641) ∨ p2651 ∨ (¬ p3487) ∨ (¬ p3506) ∨ p2528)
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p2528 ∨ p2651 ∨ p3461 ∨ (¬ p2509) ∨ (¬ p3506) ∨ (¬ p3487) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4330 := h106329;
    let u10 : (¬ p4421) := (Or.elim h98162 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (u1 r8))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111963 (p2331 p2753 p3073 p3323 p3379 p3449 p3461 p3506 p4117 p4330 p4421 : Prop)
    (h106329 : p4330)
    (h99063 : p3461 ∨ (¬ p3506) ∨ (¬ p4421) ∨ p3073 ∨ (¬ p2753) ∨ (¬ p2331) ∨ p3449 ∨ (¬ p4117) ∨ (¬ p4330) ∨ (¬ p3379))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3073 ∨ p3449 ∨ p3461 ∨ (¬ p2331) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4330 := h106329;
    let u10 : (¬ p4421) := (Or.elim h99063 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111964 (p2249 p2417 p2641 p2651 p2922 p3323 p3461 p3487 p3506 p4421 p4621 : Prop)
    (h106513 : p2249)
    (h105407 : p4621)
    (h100073 : p2417 ∨ p3461 ∨ p2651 ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p4421) ∨ (¬ p3506) ∨ (¬ p3487) ∨ (¬ p4621) ∨ p2922)
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p2417 ∨ p2922 ∨ p2651 ∨ (¬ p2641) ∨ p3461 ∨ (¬ p3506) ∨ (¬ p3487) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4621 := h105407;
    let u10 : (¬ p4421) := (Or.elim h100073 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111965 (p2230 p2331 p2427 p3246 p3323 p3461 p3506 p4117 p4421 p4621 p4729 : Prop)
    (h105407 : p4621)
    (h105429 : p4729)
    (h100741 : (¬ p3506) ∨ p3461 ∨ p2230 ∨ (¬ p4621) ∨ p3246 ∨ (¬ p4729) ∨ p2427 ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p4421))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p2427 ∨ (¬ p2331) ∨ p3461 ∨ (¬ p3506) ∨ p3246 ∨ (¬ p4117) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4621 := h105407;
    let u9 : p4729 := h105429;
    let u10 : (¬ p4421) := (Or.elim h100741 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => r8))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111968 (p2331 p2427 p2982 p3051 p3323 p3461 p3506 p3904 p4117 p4368 p4421 p4729 : Prop)
    (h105429 : p4729)
    (h94561 : p3461 ∨ (¬ p3506) ∨ (¬ p3904) ∨ (¬ p4421) ∨ (¬ p4368) ∨ p2982 ∨ (¬ p2427) ∨ (¬ p4729) ∨ (¬ p2331) ∨ p3051 ∨ (¬ p4117))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3506) ∨ p3051 ∨ (¬ p2427) ∨ (¬ p2331) ∨ p2982 ∨ (¬ p4117) ∨ p3461 ∨ (¬ p3904) ∨ (¬ p4368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4729 := h105429;
    let u11 : (¬ p4421) := (Or.elim h94561 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111971 (p2156 p2246 p2608 p2744 p2958 p3323 p3399 p3461 p3506 p3631 p3745 p4421 p4621 : Prop)
    (h106503 : p2744)
    (h105407 : p4621)
    (h82339 : (¬ p3506) ∨ p3461 ∨ p3631 ∨ p3399 ∨ (¬ p2156) ∨ (¬ p4621) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p2608) ∨ (¬ p4421) ∨ (¬ p3745))
    (h95302 : p4421 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3461 ∨ p3399 ∨ (¬ p2156) ∨ (¬ p2608) ∨ p3631 ∨ (¬ p3506) ∨ (¬ p2246) ∨ (¬ p2958) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4621 := h105407;
    let u12 : (¬ p4421) := (Or.elim h82339 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (False.elim (r10 u9))))))))))))))))))))))));
    (Or.elim h95302 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step111972 (p2098 p2132 p2619 p4359 : Prop)
    (h89708 : (¬ p2098) ∨ p2132 ∨ (¬ p4359))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p2098) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4359) := (Or.elim h89708 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96150 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111973 (p2619 p2839 p3537 p4359 : Prop)
    (h89733 : (¬ p3537) ∨ (¬ p4359) ∨ p2839)
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3537) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4359) := (Or.elim h89733 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96150 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111974 (p2132 p2619 p3366 p3537 p4359 : Prop)
    (h89799 : (¬ p3537) ∨ p2132 ∨ (¬ p3366) ∨ (¬ p4359))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3537) ∨ p2132 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4359) := (Or.elim h89799 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h96150 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111975 (p2532 p2619 p3105 p3609 p4359 : Prop)
    (h93737 : p3609 ∨ (¬ p4359) ∨ (¬ p2532) ∨ (¬ p3105))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p3105) ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4359) := (Or.elim h93737 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111976 (p2220 p2619 p3146 p3609 p4359 : Prop)
    (h93739 : (¬ p4359) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p3609)
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3146) ∨ (¬ p2220) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4359) := (Or.elim h93739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111978 (p2619 p2860 p3073 p3449 p3609 p4359 : Prop)
    (h93733 : p3609 ∨ (¬ p3073) ∨ (¬ p2860) ∨ (¬ p3449) ∨ (¬ p4359))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3073) ∨ (¬ p3449) ∨ p3609 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4359) := (Or.elim h93733 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111979 (p2608 p2619 p2839 p3146 p3609 p4359 : Prop)
    (h93734 : p3609 ∨ p2608 ∨ p2839 ∨ (¬ p3146) ∨ (¬ p4359))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p3146) ∨ p2839 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4359) := (Or.elim h93734 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111980 (p2619 p3146 p3156 p3609 p4359 p4906 : Prop)
    (h105632 : p4906)
    (h93738 : p3609 ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p3156) ∨ (¬ p4906))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3156) ∨ p3609 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    let u5 : (¬ p4359) := (Or.elim h93738 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111981 (p2088 p2619 p2860 p3609 p3696 p4359 : Prop)
    (h93742 : p3609 ∨ (¬ p3696) ∨ (¬ p4359) ∨ (¬ p2860) ∨ (¬ p2088))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p2088) ∨ (¬ p2860) ∨ (¬ p3696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4359) := (Or.elim h93742 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111983 (p2373 p2619 p3696 p3998 p4359 p4882 p5612 : Prop)
    (h105453 : p4882)
    (h61763 : (¬ p2373) ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p4359) ∨ (¬ p4882) ∨ (¬ p5612))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p2373) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    let u6 : (¬ p4359) := (Or.elim h61763 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111984 (p2088 p2166 p2619 p3609 p3696 p4359 p4878 : Prop)
    (h105452 : p4878)
    (h84610 : p3609 ∨ (¬ p3696) ∨ (¬ p2166) ∨ (¬ p4878) ∨ (¬ p4359) ∨ (¬ p2088))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p2166) ∨ (¬ p2088) ∨ (¬ p3696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4878 := h105452;
    let u6 : (¬ p4359) := (Or.elim h84610 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111986 (p2088 p2619 p3156 p3609 p3696 p4359 p4906 : Prop)
    (h105632 : p4906)
    (h93741 : p3609 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p4906) ∨ (¬ p3696) ∨ (¬ p4359))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4906 := h105632;
    let u6 : (¬ p4359) := (Or.elim h93741 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111987 (p2619 p2870 p3073 p3093 p3609 p4317 p4359 : Prop)
    (h93746 : (¬ p4317) ∨ (¬ p3073) ∨ (¬ p4359) ∨ p3609 ∨ (¬ p2870) ∨ (¬ p3093))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3073) ∨ p3609 ∨ (¬ p3093) ∨ (¬ p2870) ∨ (¬ p4317) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4359) := (Or.elim h93746 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111993 (p2619 p2751 p2996 p3256 p3609 p4044 p4359 p4392 : Prop)
    (h106343 : p2751)
    (h86921 : p3609 ∨ (¬ p4044) ∨ (¬ p4359) ∨ p2996 ∨ (¬ p3256) ∨ (¬ p2751) ∨ (¬ p4392))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p4044) ∨ p3609 ∨ (¬ p3256) ∨ p2996 ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2751 := h106343;
    let u7 : (¬ p4359) := (Or.elim h86921 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step111996 (p2619 p2922 p3073 p3609 p3695 p4359 p4644 p4688 : Prop)
    (h105411 : p4644)
    (h95456 : (¬ p4688) ∨ (¬ p3695) ∨ (¬ p4644) ∨ p2922 ∨ (¬ p3073) ∨ (¬ p4359) ∨ p3609)
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p4688) ∨ p3609 ∨ (¬ p3073) ∨ (¬ p3695) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p4688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4644 := h105411;
    let u7 : (¬ p4359) := (Or.elim h95456 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112000 (p2088 p2578 p2619 p2870 p3073 p3096 p3537 p4114 p4359 : Prop)
    (h109697 : (¬ p3537) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p4359) ∨ (¬ p3096) ∨ (¬ p2578) ∨ (¬ p4114) ∨ (¬ p2870))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3537) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3096) ∨ (¬ p2578) ∨ (¬ p4114) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4359) := (Or.elim h109697 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112001 (p2132 p2177 p2619 p3093 p3146 p3309 p3609 p4359 p4736 p4905 : Prop)
    (h105431 : p4736)
    (h105995 : p4905)
    (h81825 : p3609 ∨ (¬ p3309) ∨ (¬ p4736) ∨ p2132 ∨ (¬ p3093) ∨ (¬ p4359) ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p2177))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p3146) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p2177) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4905 := h105995;
    let u9 : (¬ p4359) := (Or.elim h81825 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112002 (p2132 p2241 p2264 p2619 p2996 p3146 p3609 p4359 p4736 p4905 : Prop)
    (h105431 : p4736)
    (h105995 : p4905)
    (h82135 : p3609 ∨ p2132 ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) ∨ (¬ p2241) ∨ (¬ p2264) ∨ p2996)
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3609 ∨ (¬ p3146) ∨ p2132 ∨ (¬ p2264) ∨ p2996 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4905 := h105995;
    let u9 : (¬ p4359) := (Or.elim h82135 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (u5 r7))))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112004 (p2132 p2619 p2911 p2922 p3146 p3379 p3609 p4359 p4736 p4905 : Prop)
    (h105431 : p4736)
    (h105995 : p4905)
    (h93747 : p3609 ∨ p2132 ∨ (¬ p2911) ∨ (¬ p4905) ∨ (¬ p2922) ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p3379) ∨ (¬ p4736))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p3146) ∨ (¬ p3379) ∨ p2132 ∨ (¬ p2911) ∨ (¬ p2922) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4905 := h105995;
    let u9 : (¬ p4359) := (Or.elim h93747 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112008 (p2088 p2190 p2241 p2619 p2870 p2992 p3156 p3609 p4114 p4359 p4558 p5017 : Prop)
    (h105400 : p4558)
    (h97130 : (¬ p4114) ∨ (¬ p2190) ∨ (¬ p5017) ∨ (¬ p4359) ∨ (¬ p2088) ∨ p3156 ∨ p2992 ∨ (¬ p2870) ∨ p2241 ∨ p3609 ∨ (¬ p4558))
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ p3156 ∨ p3609 ∨ (¬ p5017) ∨ (¬ p2088) ∨ (¬ p2870) ∨ (¬ p2190) ∨ (¬ p4114) ∨ p2992 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4558 := h105400;
    let u11 : (¬ p4359) := (Or.elim h97130 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112009 (p2088 p2427 p2493 p2619 p2860 p3379 p3609 p3660 p4359 p4555 p4590 p5207 : Prop)
    (h105542 : p4555)
    (h105491 : p5207)
    (h97203 : p3609 ∨ (¬ p5207) ∨ p3379 ∨ (¬ p3660) ∨ (¬ p4590) ∨ p2493 ∨ (¬ p4359) ∨ (¬ p2088) ∨ (¬ p4555) ∨ (¬ p2860) ∨ p2427)
    (h96150 : p4359 ∨ p2619)
    : p2619 ∨ (¬ p4590) ∨ p3609 ∨ p2493 ∨ p3379 ∨ (¬ p2860) ∨ (¬ p2088) ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4555 := h105542;
    let u10 : p5207 := h105491;
    let u11 : (¬ p4359) := (Or.elim h97203 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (u8 r9))))))))))))))))))))));
    (Or.elim h96150 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112013 (p3670 p3755 p5284 p5454 : Prop)
    (h96183 : (¬ p3670) ∨ (¬ p5284) ∨ (¬ p5454))
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ (¬ p3670) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5454) := (Or.elim h96183 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102612 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112018 (p2737 p2946 p3286 p3599 p3755 p5454 : Prop)
    (h96180 : p3599 ∨ (¬ p3286) ∨ (¬ p2737) ∨ (¬ p5454) ∨ p2946)
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ p3599 ∨ (¬ p2737) ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5454) := (Or.elim h96180 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102612 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112023 (p2807 p3246 p3286 p3434 p3755 p5454 : Prop)
    (h109609 : (¬ p3434) ∨ (¬ p5454) ∨ p3246 ∨ p2807 ∨ (¬ p3286))
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ (¬ p3434) ∨ p3246 ∨ p2807 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5454) := (Or.elim h109609 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102612 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112024 (p3323 p3461 p3564 p3670 p3755 p5454 : Prop)
    (h111945 : (¬ p3323) ∨ p3461 ∨ (¬ p5454) ∨ (¬ p3670) ∨ p3564)
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ (¬ p3323) ∨ p3461 ∨ (¬ p3670) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5454) := (Or.elim h111945 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102612 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112035 (p2274 p2307 p3125 p3276 p3286 p3564 p3670 p3755 p4117 p5454 : Prop)
    (h110047 : p3564 ∨ p3276 ∨ (¬ p5454) ∨ (¬ p2274) ∨ p3125 ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p3670) ∨ p2307)
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ p3564 ∨ p3276 ∨ (¬ p2274) ∨ p3125 ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p3670) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5454) := (Or.elim h110047 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h102612 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112039 (p2341 p2396 p2881 p3276 p3286 p3670 p3755 p4117 p4275 p4638 p5260 p5454 : Prop)
    (h105409 : p4638)
    (h96177 : p3276 ∨ p2396 ∨ (¬ p5260) ∨ (¬ p4275) ∨ (¬ p2881) ∨ (¬ p4638) ∨ (¬ p3670) ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p5454) ∨ p2341)
    (h102612 : p5454 ∨ p3755)
    : p3755 ∨ p3276 ∨ p2341 ∨ p2396 ∨ (¬ p5260) ∨ (¬ p4117) ∨ (¬ p3670) ∨ (¬ p4275) ∨ (¬ p3286) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4638 := h105409;
    let u11 : (¬ p5454) := (Or.elim h96177 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (u2 r9))))))))))))))))))))));
    (Or.elim h102612 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112054 (p2166 p3073 p3146 p4446 : Prop)
    (h93535 : p3073 ∨ (¬ p3146) ∨ (¬ p4446))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3073 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4446) := (Or.elim h93535 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102418 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112056 (p2166 p2210 p2373 p3449 p4446 p4632 : Prop)
    (h106257 : p4632)
    (h76910 : (¬ p3449) ∨ p2210 ∨ p2373 ∨ (¬ p4446) ∨ (¬ p4632))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ p2210 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    let u5 : (¬ p4446) := (Or.elim h76910 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112058 (p2166 p2373 p2563 p2668 p4446 p4993 : Prop)
    (h79019 : p2373 ∨ (¬ p4446) ∨ (¬ p4993) ∨ (¬ p2668) ∨ (¬ p2563))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p4993) ∨ p2373 ∨ (¬ p2563) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4446) := (Or.elim h79019 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112059 (p2166 p2241 p2284 p3156 p3449 p4446 : Prop)
    (h79069 : p3156 ∨ p2241 ∨ (¬ p4446) ∨ (¬ p2284) ∨ (¬ p3449))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ (¬ p2284) ∨ p2241 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4446) := (Or.elim h79069 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112060 (p2166 p2192 p2210 p3449 p4446 p4509 : Prop)
    (h105392 : p4509)
    (h80075 : (¬ p3449) ∨ p2210 ∨ p2192 ∨ (¬ p4446) ∨ (¬ p4509))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ p2192 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    let u5 : (¬ p4446) := (Or.elim h80075 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112063 (p2166 p2210 p2619 p3449 p4446 p4878 : Prop)
    (h105452 : p4878)
    (h84829 : (¬ p3449) ∨ p2210 ∨ (¬ p4878) ∨ (¬ p4446) ∨ p2619)
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ p2210 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    let u5 : (¬ p4446) := (Or.elim h84829 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112067 (p2166 p2210 p3156 p3449 p4418 p4446 p5053 : Prop)
    (h80760 : (¬ p3449) ∨ p2210 ∨ (¬ p4418) ∨ p3156 ∨ (¬ p4446) ∨ (¬ p5053))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ p2210 ∨ (¬ p5053) ∨ p3156 ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4446) := (Or.elim h80760 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112069 (p2166 p2177 p3146 p3858 p3941 p4446 p5590 : Prop)
    (h59273 : (¬ p2177) ∨ (¬ p3146) ∨ (¬ p3858) ∨ (¬ p3941) ∨ (¬ p4446) ∨ (¬ p5590))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p5590) ∨ (¬ p3858) ∨ (¬ p3941) ∨ (¬ p3146) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4446) := (Or.elim h59273 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112071 (p2166 p2528 p3073 p3156 p4355 p4446 p4702 : Prop)
    (h106079 : p4702)
    (h93534 : p3073 ∨ (¬ p2528) ∨ (¬ p4446) ∨ (¬ p4702) ∨ (¬ p4355) ∨ p3156)
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3073 ∨ (¬ p2528) ∨ (¬ p4355) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    let u6 : (¬ p4446) := (Or.elim h93534 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112086 (p2166 p2241 p2459 p2717 p2744 p3366 p3425 p3449 p3969 p4446 p5122 : Prop)
    (h106503 : p2744)
    (h105483 : p5122)
    (h97070 : (¬ p5122) ∨ (¬ p3449) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p2744) ∨ p2459 ∨ p2717 ∨ (¬ p3366) ∨ (¬ p4446) ∨ p2241)
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ (¬ p3425) ∨ p2717 ∨ p2459 ∨ (¬ p3366) ∨ (¬ p3969) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p5122 := h105483;
    let u10 : (¬ p4446) := (Or.elim h97070 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u7 r8))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112087 (p2166 p2210 p2417 p2598 p3146 p3201 p3366 p3449 p4377 p4446 p4669 : Prop)
    (h105415 : p4669)
    (h106170 : p4377)
    (h100085 : p2210 ∨ p3201 ∨ (¬ p4669) ∨ (¬ p4446) ∨ p2598 ∨ (¬ p3449) ∨ (¬ p3366) ∨ p2417 ∨ (¬ p3146) ∨ (¬ p4377))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p3201 ∨ p2417 ∨ (¬ p3146) ∨ p2210 ∨ (¬ p3449) ∨ (¬ p3366) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    let u9 : p4377 := h106170;
    let u10 : (¬ p4446) := (Or.elim h100085 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112088 (p2166 p2210 p2363 p2774 p2819 p3366 p3449 p3969 p4377 p4446 p5122 : Prop)
    (h106170 : p4377)
    (h105483 : p5122)
    (h100838 : (¬ p3969) ∨ (¬ p3449) ∨ (¬ p5122) ∨ p2363 ∨ p2210 ∨ (¬ p4446) ∨ p2774 ∨ p2819 ∨ (¬ p3366) ∨ (¬ p4377))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2819 ∨ p2363 ∨ p2774 ∨ p2210 ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    let u9 : p5122 := h105483;
    let u10 : (¬ p4446) := (Or.elim h100838 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112089 (p2166 p2363 p2774 p2819 p3366 p3379 p3449 p3969 p4376 p4446 p5122 : Prop)
    (h106320 : p4376)
    (h105483 : p5122)
    (h100839 : (¬ p3969) ∨ p2363 ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p5122) ∨ (¬ p4446) ∨ p3379 ∨ p2819 ∨ p2774 ∨ (¬ p4376))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2819 ∨ p2363 ∨ p3379 ∨ p2774 ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5122 := h105483;
    let u10 : (¬ p4446) := (Or.elim h100839 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112091 (p2166 p2210 p2449 p2685 p2696 p3146 p3366 p3449 p4377 p4446 p4669 : Prop)
    (h105415 : p4669)
    (h106170 : p4377)
    (h101627 : (¬ p4446) ∨ p2449 ∨ p2210 ∨ p2685 ∨ p2696 ∨ (¬ p4669) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p3449))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2685 ∨ p2449 ∨ p2210 ∨ (¬ p3146) ∨ (¬ p3449) ∨ (¬ p3366) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    let u9 : p4377 := h106170;
    let u10 : (¬ p4446) := (Or.elim h101627 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112094 (p2166 p2210 p2417 p2651 p3146 p3201 p3366 p3449 p3683 p4236 p4377 p4446 p4669 : Prop)
    (h105415 : p4669)
    (h106170 : p4377)
    (h100062 : (¬ p4236) ∨ (¬ p3449) ∨ (¬ p4446) ∨ p2651 ∨ p2210 ∨ (¬ p3146) ∨ (¬ p3683) ∨ p3201 ∨ p2417 ∨ (¬ p4377) ∨ (¬ p4669) ∨ (¬ p3366))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ p2417 ∨ (¬ p3683) ∨ p2210 ∨ p3201 ∨ (¬ p3146) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p4236) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4669 := h105415;
    let u11 : p4377 := h106170;
    let u12 : (¬ p4446) := (Or.elim h100062 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (False.elim (r10 u7))))))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112095 (p2166 p2210 p2651 p3146 p3366 p3422 p3449 p3564 p3683 p4236 p4377 p4446 p4604 : Prop)
    (h106293 : p4604)
    (h106170 : p4377)
    (h101454 : p3564 ∨ p2651 ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p4604) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p3146) ∨ p2210 ∨ p3422 ∨ (¬ p4446) ∨ (¬ p3683))
    (h102418 : p4446 ∨ (¬ p2166))
    : (¬ p2166) ∨ (¬ p3449) ∨ p3564 ∨ p3422 ∨ p2651 ∨ p2210 ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3683) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4604 := h106293;
    let u11 : p4377 := h106170;
    let u12 : (¬ p4446) := (Or.elim h101454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (False.elim (r10 u9))))))))))))))))))))))));
    (Or.elim h102418 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112096 (p2264 p2459 p3256 p4548 : Prop)
    (h75187 : (¬ p4548) ∨ (¬ p3256) ∨ p2459)
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p2459 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4548) := (Or.elim h75187 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h95329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112098 (p2177 p2264 p2996 p3189 p4548 : Prop)
    (h81972 : p2996 ∨ p3189 ∨ (¬ p2177) ∨ (¬ p4548))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3189 ∨ (¬ p2177) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4548) := (Or.elim h81972 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h95329 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112100 (p2177 p2264 p2807 p3166 p4548 : Prop)
    (h101948 : p3166 ∨ (¬ p2177) ∨ (¬ p4548) ∨ (¬ p2807))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4548) := (Or.elim h101948 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112101 (p2264 p2881 p2996 p3189 p4280 p4548 : Prop)
    (h105599 : p4280)
    (h81965 : p2996 ∨ p3189 ∨ (¬ p4548) ∨ (¬ p2881) ∨ (¬ p4280))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3189 ∨ (¬ p2881) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    let u5 : (¬ p4548) := (Or.elim h81965 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112104 (p2264 p2449 p2807 p3166 p4548 p4668 : Prop)
    (h105414 : p4668)
    (h86553 : p3166 ∨ (¬ p2449) ∨ (¬ p4548) ∨ (¬ p4668) ∨ (¬ p2807))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p2449) ∨ (¬ p2807) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4548) := (Or.elim h86553 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112105 (p2264 p2449 p2685 p3005 p4548 p4668 : Prop)
    (h105414 : p4668)
    (h89041 : p3005 ∨ (¬ p2449) ∨ (¬ p4668) ∨ (¬ p4548) ∨ (¬ p2685))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p2449) ∨ p3005 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4548) := (Or.elim h89041 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112106 (p2264 p2685 p2881 p3005 p4280 p4548 : Prop)
    (h105599 : p4280)
    (h89067 : p3005 ∨ (¬ p4280) ∨ (¬ p2685) ∨ (¬ p2881) ∨ (¬ p4548))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3005 ∨ (¬ p2881) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    let u5 : (¬ p4548) := (Or.elim h89067 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112107 (p2264 p2685 p3005 p3040 p3527 p4548 : Prop)
    (h89068 : p3005 ∨ (¬ p3527) ∨ (¬ p2685) ∨ (¬ p4548) ∨ (¬ p3040))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p3527) ∨ (¬ p2685) ∨ (¬ p3040) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4548) := (Or.elim h89068 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112108 (p2264 p2685 p3005 p3931 p4548 p5564 : Prop)
    (h89077 : (¬ p3931) ∨ (¬ p5564) ∨ p3005 ∨ (¬ p4548) ∨ (¬ p2685))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p3931) ∨ (¬ p5564) ∨ (¬ p2685) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4548) := (Or.elim h89077 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112109 (p2264 p2807 p2911 p3166 p4327 p4548 : Prop)
    (h105381 : p4327)
    (h95143 : p3166 ∨ (¬ p2911) ∨ (¬ p4327) ∨ (¬ p2807) ∨ (¬ p4548))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4327 := h105381;
    let u5 : (¬ p4548) := (Or.elim h95143 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112112 (p2264 p2331 p2630 p2797 p3166 p4548 : Prop)
    (h101578 : p2797 ∨ p3166 ∨ (¬ p2331) ∨ (¬ p2630) ∨ (¬ p4548))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3166 ∨ p2797 ∨ (¬ p2331) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4548) := (Or.elim h101578 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112113 (p2264 p2630 p2651 p2911 p3166 p4548 : Prop)
    (h101949 : p3166 ∨ (¬ p2911) ∨ (¬ p2651) ∨ (¬ p4548) ∨ p2630)
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p2911) ∨ p3166 ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4548) := (Or.elim h101949 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112114 (p2264 p2807 p2881 p3166 p4280 p4548 : Prop)
    (h105599 : p4280)
    (h101956 : p3166 ∨ (¬ p2881) ∨ (¬ p4548) ∨ (¬ p4280) ∨ (¬ p2807))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    let u5 : (¬ p4548) := (Or.elim h101956 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112120 (p2264 p2685 p3005 p3246 p3657 p4280 p4548 : Prop)
    (h105599 : p4280)
    (h89038 : p3005 ∨ (¬ p3246) ∨ (¬ p3657) ∨ (¬ p4548) ∨ (¬ p2685) ∨ (¬ p4280))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p3246) ∨ (¬ p3657) ∨ p3005 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4280 := h105599;
    let u6 : (¬ p4548) := (Or.elim h89038 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112122 (p2264 p2630 p2651 p2911 p3005 p4236 p4548 : Prop)
    (h98136 : (¬ p2911) ∨ p2651 ∨ p3005 ∨ (¬ p2630) ∨ (¬ p4548) ∨ (¬ p4236))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ p3005 ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2911) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4548) := (Or.elim h98136 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112126 (p2177 p2264 p2315 p3961 p4009 p4548 p5590 : Prop)
    (h105368 : p2315)
    (h58246 : (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3961) ∨ (¬ p4009) ∨ (¬ p4548) ∨ (¬ p5590))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p4009) ∨ (¬ p3961) ∨ (¬ p2177) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2315 := h105368;
    let u6 : (¬ p4548) := (Or.elim h58246 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112136 (p2177 p2230 p2252 p2264 p2331 p2373 p2741 p2797 p3005 p3146 p3519 p4376 p4548 : Prop)
    (h106320 : p4376)
    (h101091 : p3005 ∨ (¬ p2373) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p2741) ∨ (¬ p2252) ∨ (¬ p2797) ∨ (¬ p2177) ∨ (¬ p2230) ∨ p2331 ∨ (¬ p4548) ∨ (¬ p3146))
    (h95329 : p4548 ∨ p2264)
    : p2264 ∨ (¬ p2177) ∨ (¬ p2252) ∨ p2331 ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p2230) ∨ p3005 ∨ (¬ p3519) ∨ (¬ p2797) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4376 := h106320;
    let u12 : (¬ p4548) := (Or.elim h101091 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (False.elim (r10 u4))))))))))))))))))))))));
    (Or.elim h95329 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112138 (p3177 p3189 p3858 p5074 : Prop)
    (h35060 : (¬ p3177) ∨ p3858 ∨ (¬ p5074))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p3858 ∨ (¬ p3177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3858) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5074) := (Or.elim h35060 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h87329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112139 (p3189 p4009 p4181 p5074 : Prop)
    (h40760 : p4009 ∨ (¬ p4181) ∨ (¬ p5074))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p4009 ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4009) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5074) := (Or.elim h40760 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h87329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112140 (p3073 p3189 p3256 p5074 : Prop)
    (h110468 : (¬ p3073) ∨ (¬ p5074) ∨ p3256)
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p3073) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5074) := (Or.elim h110468 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h87329 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112141 (p2253 p3166 p3189 p3449 p5074 : Prop)
    (h100024 : p3449 ∨ (¬ p5074) ∨ (¬ p2253) ∨ (¬ p3166))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p3449 ∨ (¬ p3166) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5074) := (Or.elim h100024 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112144 (p2241 p2745 p3005 p3189 p3449 p5074 : Prop)
    (h105523 : p2745)
    (h80608 : (¬ p5074) ∨ (¬ p3005) ∨ p3449 ∨ (¬ p2241) ∨ (¬ p2745))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p3005) ∨ p3449 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    let u5 : (¬ p5074) := (Or.elim h80608 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112145 (p2187 p2331 p3166 p3189 p4318 p5074 : Prop)
    (h92355 : (¬ p4318) ∨ (¬ p5074) ∨ p2331 ∨ p2187 ∨ (¬ p3166))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p4318) ∨ p2187 ∨ p2331 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5074) := (Or.elim h92355 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112147 (p2807 p2911 p3166 p3189 p3527 p5074 : Prop)
    (h111029 : (¬ p3527) ∨ (¬ p5074) ∨ p2911 ∨ p2807 ∨ (¬ p3166))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p3527) ∨ p2911 ∨ p2807 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5074) := (Or.elim h111029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112149 (p2651 p3166 p3189 p3641 p4687 p4750 p5074 : Prop)
    (h105433 : p4750)
    (h95419 : (¬ p4687) ∨ (¬ p5074) ∨ p3641 ∨ p2651 ∨ (¬ p4750) ∨ (¬ p3166))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p4687) ∨ p3641 ∨ p2651 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : (¬ p5074) := (Or.elim h95419 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112151 (p2241 p2630 p2748 p3189 p3449 p5008 p5074 : Prop)
    (h105469 : p5008)
    (h101518 : p3449 ∨ (¬ p5074) ∨ (¬ p2748) ∨ (¬ p2241) ∨ (¬ p5008) ∨ (¬ p2630))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p3449 ∨ (¬ p2748) ∨ (¬ p2241) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5008 := h105469;
    let u6 : (¬ p5074) := (Or.elim h101518 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112164 (p2255 p2662 p2727 p3073 p3166 p3189 p3266 p3389 p4831 p5074 p5503 : Prop)
    (h105367 : p2255)
    (h105445 : p4831)
    (h76593 : (¬ p5503) ∨ (¬ p3266) ∨ (¬ p3166) ∨ (¬ p3073) ∨ p2727 ∨ (¬ p5074) ∨ (¬ p4831) ∨ (¬ p2255) ∨ (¬ p2662) ∨ p3389)
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p5503) ∨ (¬ p3266) ∨ (¬ p3166) ∨ p2727 ∨ (¬ p2662) ∨ p3389 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4831 := h105445;
    let u10 : (¬ p5074) := (Or.elim h76593 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112168 (p2255 p2363 p2881 p2957 p2992 p3051 p3073 p3166 p3189 p4133 p5074 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h80191 : (¬ p3073) ∨ p2363 ∨ p2992 ∨ (¬ p3166) ∨ (¬ p4133) ∨ p2881 ∨ (¬ p5074) ∨ p3051 ∨ (¬ p2957) ∨ (¬ p2255))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p2363 ∨ p3051 ∨ p2992 ∨ (¬ p3166) ∨ (¬ p3073) ∨ (¬ p2957) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4133 := h105712;
    let u10 : (¬ p5074) := (Or.elim h80191 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112169 (p2241 p2449 p2750 p2839 p2870 p2881 p3189 p3449 p4044 p4666 p5074 : Prop)
    (h106345 : p2750)
    (h105658 : p4666)
    (h83769 : p2449 ∨ (¬ p4044) ∨ (¬ p2241) ∨ (¬ p2870) ∨ (¬ p2839) ∨ (¬ p4666) ∨ (¬ p2750) ∨ p3449 ∨ (¬ p2881) ∨ (¬ p5074))
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ p3449 ∨ p2449 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2241) ∨ (¬ p2839) ∨ (¬ p4044) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4666 := h105658;
    let u10 : (¬ p5074) := (Or.elim h83769 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => r8))))))))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112173 (p2177 p2241 p2717 p2753 p3189 p3425 p3449 p4149 p5074 p5506 p5600 : Prop)
    (h108762 : (¬ p5506) ∨ (¬ p4149) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ (¬ p5074) ∨ p2177)
    (h87329 : p5074 ∨ p3189)
    : p3189 ∨ (¬ p5506) ∨ (¬ p4149) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p5506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5074) := (Or.elim h108762 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h87329 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112183 (p2177 p2417 p2449 p2911 p3192 : Prop)
    (h111709 : (¬ p2417) ∨ (¬ p3192) ∨ (¬ p2177) ∨ p2911 ∨ p2449)
    (h96425 : p3192 ∨ (¬ p2417))
    : (¬ p2417) ∨ (¬ p2177) ∨ p2911 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3192) := (Or.elim h111709 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96425 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112185 (p2264 p4378 p5558 p5600 : Prop)
    (h30915 : (¬ p4378) ∨ p5558 ∨ (¬ p5600))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ p5558 ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5558) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4378) := (Or.elim h30915 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96456 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112187 (p2264 p2459 p3256 p4378 : Prop)
    (h40560 : (¬ p2459) ∨ p3256 ∨ (¬ p4378))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3256 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4378) := (Or.elim h40560 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96456 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112196 (p2177 p2264 p2651 p2727 p3189 p4378 : Prop)
    (h91893 : p2727 ∨ (¬ p4378) ∨ p2177 ∨ (¬ p3189) ∨ (¬ p2651))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3189) ∨ p2177 ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4378) := (Or.elim h91893 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112197 (p2264 p2911 p2996 p3189 p4378 p4653 : Prop)
    (h91966 : (¬ p4378) ∨ (¬ p3189) ∨ p2911 ∨ (¬ p2996) ∨ (¬ p4653))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3189) ∨ (¬ p2996) ∨ (¬ p4653) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4378) := (Or.elim h91966 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112202 (p2264 p2449 p2685 p3005 p4378 p4666 : Prop)
    (h105658 : p4666)
    (h100160 : (¬ p3005) ∨ (¬ p4378) ∨ (¬ p4666) ∨ p2449 ∨ p2685)
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3005) ∨ p2685 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    let u5 : (¬ p4378) := (Or.elim h100160 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112203 (p2264 p2807 p2996 p3166 p3527 p4378 : Prop)
    (h109376 : (¬ p2996) ∨ p3527 ∨ (¬ p4378) ∨ p2807 ∨ (¬ p3166))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2996) ∨ p3527 ∨ p2807 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4378) := (Or.elim h109376 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112210 (p2264 p2619 p2870 p2911 p4277 p4312 p4378 : Prop)
    (h105380 : p4277)
    (h86675 : (¬ p4378) ∨ (¬ p4312) ∨ (¬ p2619) ∨ p2870 ∨ (¬ p4277) ∨ p2911)
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p2619) ∨ p2870 ∨ p2911 ∨ (¬ p4312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4277 := h105380;
    let u6 : (¬ p4378) := (Or.elim h86675 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112211 (p2177 p2253 p2264 p2331 p2641 p3189 p4378 : Prop)
    (h92005 : (¬ p4378) ∨ p2641 ∨ (¬ p2331) ∨ p2177 ∨ (¬ p2253) ∨ (¬ p3189))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p3189) ∨ p2177 ∨ (¬ p2331) ∨ p2641 ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4378) := (Or.elim h92005 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112214 (p2264 p2363 p2911 p3256 p3325 p4276 p4378 : Prop)
    (h105516 : p4276)
    (h101399 : (¬ p4378) ∨ p3256 ∨ p2911 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4276))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3256 ∨ (¬ p3325) ∨ (¬ p2363) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4276 := h105516;
    let u6 : (¬ p4378) := (Or.elim h101399 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112215 (p2264 p2911 p2996 p3256 p3842 p4378 p4653 : Prop)
    (h111102 : p3256 ∨ (¬ p4378) ∨ (¬ p2996) ∨ (¬ p3842) ∨ p2911 ∨ (¬ p4653))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ p3256 ∨ (¬ p2996) ∨ (¬ p3842) ∨ p2911 ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4378) := (Or.elim h111102 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112217 (p2088 p2264 p2881 p3073 p3177 p4189 p4378 p4914 : Prop)
    (h80200 : (¬ p4378) ∨ (¬ p4189) ∨ p2088 ∨ p2881 ∨ (¬ p4914) ∨ (¬ p3073) ∨ (¬ p3177))
    (h96456 : p4378 ∨ (¬ p2264))
    : (¬ p2264) ∨ (¬ p4189) ∨ (¬ p3177) ∨ p2088 ∨ (¬ p4914) ∨ p2881 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4378) := (Or.elim h80200 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h96456 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step112230 (p3527 p3544 p4105 p4371 : Prop)
    (h28047 : (¬ p3544) ∨ (¬ p4105) ∨ p4371)
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ p4371 ∨ (¬ p4105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4371) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3544) := (Or.elim h28047 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102269 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112231 (p3399 p3449 p3527 p3544 : Prop)
    (h27565 : p3399 ∨ (¬ p3449) ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p3449) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3544) := (Or.elim h27565 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h102269 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112233 (p2341 p3527 p3542 p3543 p3544 : Prop)
    (h5164 : (¬ p2341) ∨ (¬ p3542) ∨ (¬ p3543) ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3542) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3544) := (Or.elim h5164 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102269 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112234 (p2241 p2459 p3073 p3399 p3527 p3544 : Prop)
    (h91613 : p3399 ∨ p3073 ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p2241))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ p3073 ∨ (¬ p2459) ∨ p3399 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h91613 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112235 (p2459 p2717 p3073 p3527 p3544 p4794 : Prop)
    (h91624 : (¬ p2717) ∨ p3073 ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p4794))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p2717) ∨ (¬ p2459) ∨ (¬ p4794) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h91624 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112238 (p2363 p3073 p3527 p3544 p4075 p4372 : Prop)
    (h97257 : (¬ p4075) ∨ (¬ p4372) ∨ p3073 ∨ (¬ p2363) ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p4075) ∨ (¬ p4372) ∨ (¬ p2363) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h97257 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112239 (p2459 p2608 p3073 p3399 p3527 p3544 : Prop)
    (h99036 : p3399 ∨ p3073 ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ p3073 ∨ p3399 ∨ (¬ p2459) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h99036 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112240 (p2459 p2881 p3073 p3527 p3544 p4911 : Prop)
    (h99044 : p3073 ∨ (¬ p3544) ∨ (¬ p2881) ∨ (¬ p4911) ∨ (¬ p2459))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p2459) ∨ p3073 ∨ (¬ p4911) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h99044 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112241 (p3073 p3146 p3527 p3544 p4075 p4372 : Prop)
    (h99087 : (¬ p4075) ∨ (¬ p4372) ∨ (¬ p3146) ∨ p3073 ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p4372) ∨ (¬ p4075) ∨ p3073 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3544) := (Or.elim h99087 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112242 (p2459 p2598 p3073 p3425 p3527 p3544 p3576 : Prop)
    (h88582 : (¬ p3576) ∨ (¬ p3544) ∨ p3073 ∨ (¬ p2598) ∨ (¬ p2459) ∨ (¬ p3425))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ p3073 ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p2459) ∨ (¬ p3576) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3544) := (Or.elim h88582 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112243 (p2881 p2933 p3527 p3544 p3941 p4277 p5693 : Prop)
    (h105380 : p4277)
    (h41768 : (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3544) ∨ (¬ p3941) ∨ (¬ p4277) ∨ (¬ p5693))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p5693) ∨ (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4277 := h105380;
    let u6 : (¬ p3544) := (Or.elim h41768 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112245 (p2363 p2911 p2930 p3073 p3527 p3544 p4138 : Prop)
    (h105376 : p2930)
    (h91623 : p3073 ∨ (¬ p3544) ∨ (¬ p4138) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2930))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p2911) ∨ p3073 ∨ (¬ p4138) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2930 := h105376;
    let u6 : (¬ p3544) := (Or.elim h91623 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112246 (p2255 p3031 p3073 p3166 p3256 p3527 p3544 : Prop)
    (h105367 : p2255)
    (h91625 : p3073 ∨ (¬ p3031) ∨ (¬ p2255) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p3544))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p3031) ∨ p3073 ∨ (¬ p3256) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    let u6 : (¬ p3544) := (Or.elim h91625 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step112247 (p2619 p3527 p3544 p3554 p3969 p4875 p5693 : Prop)
    (h106227 : p4875)
    (h41763 : (¬ p2619) ∨ (¬ p3544) ∨ (¬ p3554) ∨ (¬ p3969) ∨ (¬ p4875) ∨ (¬ p5693))
    (h102269 : p3544 ∨ p3527)
    : p3527 ∨ (¬ p2619) ∨ (¬ p5693) ∨ (¬ p3969) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4875 := h106227;
    let u6 : (¬ p3544) := (Or.elim h41763 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

end ElevenRUP
