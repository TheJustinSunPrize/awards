import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step123337 (p2192 p2881 p3527 p3554 p4555 : Prop)
    (h105542 : p4555)
    (h93506 : p3527 ∨ (¬ p2881) ∨ (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4555))
    : p3527 ∨ (¬ p3554) ∨ (¬ p2192) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h93506 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123338 (p2192 p3246 p3554 p3631 p4555 : Prop)
    (h105542 : p4555)
    (h93509 : p3631 ∨ (¬ p3246) ∨ (¬ p4555) ∨ (¬ p2192) ∨ (¬ p3554))
    : (¬ p3554) ∨ (¬ p2192) ∨ (¬ p3246) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h93509 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123340 (p2911 p3389 p3527 p3554 p4202 p5194 : Prop)
    (h105489 : p5194)
    (h93514 : p3527 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4202) ∨ (¬ p5194) ∨ (¬ p3554))
    : (¬ p3554) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4202) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5194 := h105489;
    (Or.elim h93514 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123346 (p2156 p2190 p2363 p2598 p2911 p3146 p3201 p4133 p4172 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h93532 : (¬ p2190) ∨ p3201 ∨ p2598 ∨ p2911 ∨ (¬ p3146) ∨ (¬ p4172) ∨ (¬ p4133) ∨ (¬ p2156) ∨ p2363 ∨ (¬ p4736))
    : (¬ p2190) ∨ p3201 ∨ p2363 ∨ (¬ p4172) ∨ p2911 ∨ (¬ p3146) ∨ p2598 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4133 := h105712;
    (Or.elim h93532 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step123347 (p2341 p2901 p2911 p3741 p4283 p4702 : Prop)
    (h106079 : p4702)
    (h93542 : (¬ p2911) ∨ p2341 ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2901 ∨ (¬ p4702))
    : (¬ p4283) ∨ (¬ p2911) ∨ p2341 ∨ p2901 ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4283 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    (Or.elim h93542 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123349 (p2901 p3516 p3631 p4283 p4431 p4960 : Prop)
    (h106209 : p4960)
    (h93550 : (¬ p3631) ∨ p3516 ∨ (¬ p4431) ∨ (¬ p4960) ∨ p2901 ∨ (¬ p4283))
    : (¬ p3631) ∨ (¬ p4283) ∨ p2901 ∨ p3516 ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4960 := h106209;
    (Or.elim h93550 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step123350 (p2427 p3516 p3631 p4283 p4338 p4452 p4632 : Prop)
    (h106257 : p4632)
    (h93551 : (¬ p3631) ∨ p3516 ∨ (¬ p4452) ∨ (¬ p4283) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4338))
    : (¬ p4283) ∨ (¬ p4452) ∨ p2427 ∨ (¬ p4338) ∨ (¬ p3631) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4283 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4632 := h106257;
    (Or.elim h93551 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step123354 (p2241 p2727 p3093 p3922 p4975 : Prop)
    (h105464 : p4975)
    (h93584 : p2241 ∨ (¬ p3093) ∨ (¬ p4975) ∨ p2727 ∨ (¬ p3922))
    : p2727 ∨ (¬ p3093) ∨ (¬ p3922) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h93584 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123356 (p3922 p4514 p4564 : Prop)
    (h105401 : p4564)
    (h18259 : (¬ p3922) ∨ p4514 ∨ (¬ p4564))
    : (¬ p3922) ∨ p4514 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4514) := (fun h => hn (Or.inr h));
    let u2 : p4564 := h105401;
    (Or.elim h18259 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step123358 (p2137 p4525 p4875 : Prop)
    (h106227 : p4875)
    (h34840 : (¬ p2137) ∨ p4525 ∨ (¬ p4875))
    : (¬ p2137) ∨ p4525 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4525) := (fun h => hn (Or.inr h));
    let u2 : p4875 := h106227;
    (Or.elim h34840 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step123360 (p2137 p2187 p2295 p2641 p2696 p2748 p2839 p3051 p4204 p4405 : Prop)
    (h105512 : p4405)
    (h93602 : (¬ p3051) ∨ p2295 ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2187) ∨ (¬ p4204) ∨ p2696 ∨ (¬ p2137) ∨ (¬ p4405) ∨ p2641)
    : (¬ p2137) ∨ (¬ p2187) ∨ (¬ p4204) ∨ p2295 ∨ p2696 ∨ (¬ p2839) ∨ (¬ p2748) ∨ p2641 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4405 := h105512;
    (Or.elim h93602 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u7 r8)))))))))))))))))))))

theorem step123362 (p2781 p4736 p5020 : Prop)
    (h105431 : p4736)
    (h34674 : p2781 ∨ (¬ p4736) ∨ (¬ p5020))
    : (¬ p5020) ∨ p2781 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5020 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2781) := (fun h => hn (Or.inr h));
    let u2 : p4736 := h105431;
    (Or.elim h34674 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step123370 (p2210 p2307 p3309 p3953 p4377 p5020 : Prop)
    (h106170 : p4377)
    (h93637 : p2210 ∨ (¬ p2307) ∨ (¬ p4377) ∨ (¬ p5020) ∨ (¬ p3953) ∨ p3309)
    : p2210 ∨ (¬ p2307) ∨ (¬ p5020) ∨ p3309 ∨ (¬ p3953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4377 := h106170;
    (Or.elim h93637 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step123372 (p2122 p3309 p3367 p3953 p4426 p4752 : Prop)
    (h105434 : p4752)
    (h93640 : (¬ p3953) ∨ (¬ p2122) ∨ (¬ p3367) ∨ p3309 ∨ (¬ p4426) ∨ (¬ p4752))
    : (¬ p2122) ∨ (¬ p3953) ∨ p3309 ∨ (¬ p3367) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4752 := h105434;
    (Or.elim h93640 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123374 (p2307 p2584 p2737 p3309 p3759 p3953 p4749 : Prop)
    (h105432 : p4749)
    (h93645 : (¬ p3953) ∨ (¬ p3759) ∨ (¬ p2307) ∨ p3309 ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p2584))
    : (¬ p3953) ∨ (¬ p2737) ∨ (¬ p2584) ∨ (¬ p3759) ∨ (¬ p2307) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4749 := h105432;
    (Or.elim h93645 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step123376 (p2187 p2192 p2210 p2254 p2459 p2807 p3256 p3919 p4133 : Prop)
    (h105366 : p2254)
    (h105712 : p4133)
    (h93649 : p2807 ∨ (¬ p2187) ∨ (¬ p2254) ∨ p3256 ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4133))
    : (¬ p2192) ∨ p2807 ∨ p3256 ∨ (¬ p3919) ∨ (¬ p2459) ∨ (¬ p2210) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4133 := h105712;
    (Or.elim h93649 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step123377 (p2459 p2881 p3256 p3919 p4280 : Prop)
    (h105599 : p4280)
    (h93650 : p3256 ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p2459) ∨ (¬ p4280))
    : (¬ p2881) ∨ p3256 ∨ (¬ p2459) ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    (Or.elim h93650 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123378 (p3919 p4652 p5011 : Prop)
    (h105413 : p4652)
    (h31996 : (¬ p3919) ∨ (¬ p4652) ∨ p5011)
    : (¬ p3919) ∨ p5011 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3919 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5011) := (fun h => hn (Or.inr h));
    let u2 : p4652 := h105413;
    (Or.elim h31996 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step123391 (p2144 p2156 p2696 p2860 p5052 : Prop)
    (h105473 : p5052)
    (h93705 : p2860 ∨ (¬ p2144) ∨ (¬ p5052) ∨ (¬ p2156) ∨ p2696)
    : p2860 ∨ (¬ p2144) ∨ p2696 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5052 := h105473;
    (Or.elim h93705 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step123394 (p2144 p2156 p2252 p2264 p2750 p2807 p3125 p3366 p3461 p5123 p5558 : Prop)
    (h106345 : p2750)
    (h93710 : p3366 ∨ (¬ p3461) ∨ (¬ p2252) ∨ (¬ p5123) ∨ (¬ p5558) ∨ p2807 ∨ (¬ p2750) ∨ (¬ p2144) ∨ (¬ p3125) ∨ (¬ p2156) ∨ p2264)
    : p3366 ∨ (¬ p2252) ∨ p2264 ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2807 ∨ (¬ p2156) ∨ (¬ p2144) ∨ (¬ p5558) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3366) := (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    (Or.elim h93710 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (u2 r9)))))))))))))))))))))))

theorem step123396 (p2651 p2751 p2946 p3136 p3487 p4281 : Prop)
    (h106343 : p2751)
    (h93765 : p3136 ∨ (¬ p2946) ∨ p2651 ∨ (¬ p2751) ∨ (¬ p4281) ∨ (¬ p3487))
    : p3136 ∨ (¬ p3487) ∨ (¬ p4281) ∨ p2651 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h93765 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step123399 (p2249 p2656 p2727 p2807 p3051 p3699 p4399 : Prop)
    (h106513 : p2249)
    (h93793 : (¬ p4399) ∨ (¬ p3051) ∨ (¬ p2656) ∨ (¬ p3699) ∨ p2807 ∨ (¬ p2249) ∨ (¬ p2727))
    : p2807 ∨ (¬ p4399) ∨ (¬ p3051) ∨ (¬ p2727) ∨ (¬ p3699) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2249 := h106513;
    (Or.elim h93793 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step123403 (p3166 p3256 p3609 p4364 p4790 : Prop)
    (h106424 : p4790)
    (h93801 : p3609 ∨ (¬ p4364) ∨ (¬ p4790) ∨ (¬ p3256) ∨ (¬ p3166))
    : p3609 ∨ (¬ p4364) ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h93801 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123417 (p2230 p2331 p2363 p2427 p2819 p3246 p3366 p3519 p3950 p4236 p4328 p4376 : Prop)
    (h106320 : p4376)
    (h93873 : p2363 ∨ (¬ p4236) ∨ p2331 ∨ p2819 ∨ (¬ p3246) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p3950) ∨ (¬ p4328) ∨ (¬ p3366) ∨ (¬ p2427))
    : (¬ p3519) ∨ (¬ p3246) ∨ p2363 ∨ (¬ p2427) ∨ (¬ p2230) ∨ p2331 ∨ (¬ p3366) ∨ p2819 ∨ (¬ p4236) ∨ (¬ p4328) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3519 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4376 := h106320;
    (Or.elim h93873 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step123418 (p2187 p2230 p2563 p2630 p3005 p3166 p3366 p3519 p3979 p4236 p4376 : Prop)
    (h106320 : p4376)
    (h93874 : (¬ p3366) ∨ (¬ p2187) ∨ (¬ p3005) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p2630 ∨ (¬ p4236) ∨ p3166 ∨ (¬ p3979))
    : (¬ p3979) ∨ p3166 ∨ p2630 ∨ (¬ p3366) ∨ (¬ p2187) ∨ (¬ p3005) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p4236) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    (Or.elim h93874 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step123420 (p2220 p2459 p2630 p2651 p3005 p3146 p3366 p3370 p4041 p4236 p4377 : Prop)
    (h106170 : p4377)
    (h93876 : (¬ p3370) ∨ (¬ p3146) ∨ p2459 ∨ (¬ p4377) ∨ (¬ p3366) ∨ p3005 ∨ p2651 ∨ (¬ p2630) ∨ (¬ p2220) ∨ (¬ p4041) ∨ (¬ p4236))
    : p2651 ∨ p3005 ∨ (¬ p4236) ∨ p2459 ∨ (¬ p4041) ∨ (¬ p2220) ∨ (¬ p3366) ∨ (¬ p3146) ∨ (¬ p2630) ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4377 := h106170;
    (Or.elim h93876 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step123423 (p2143 p2696 p2742 p2839 p3051 p3189 p3246 p3256 p4669 : Prop)
    (h105415 : p4669)
    (h93924 : (¬ p3189) ∨ p3051 ∨ p2839 ∨ (¬ p3256) ∨ p3246 ∨ (¬ p2742) ∨ (¬ p4669) ∨ (¬ p2696) ∨ (¬ p2143))
    : (¬ p2143) ∨ (¬ p2696) ∨ (¬ p2742) ∨ p3051 ∨ (¬ p3189) ∨ p2839 ∨ p3246 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h93924 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step123426 (p2696 p2742 p2911 p2992 p3156 p3363 p3367 p3389 p4902 : Prop)
    (h105456 : p4902)
    (h93929 : (¬ p2992) ∨ p3367 ∨ (¬ p3156) ∨ (¬ p2696) ∨ p2911 ∨ (¬ p4902) ∨ (¬ p2742) ∨ p3389 ∨ (¬ p3363))
    : (¬ p3363) ∨ (¬ p2696) ∨ p3367 ∨ (¬ p2992) ∨ (¬ p2742) ∨ (¬ p3156) ∨ p2911 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    (Or.elim h93929 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step123429 (p2156 p2284 p2901 p2911 p3399 p3527 p4521 p4647 : Prop)
    (h105412 : p4647)
    (h93934 : (¬ p2901) ∨ p2284 ∨ p3399 ∨ (¬ p2911) ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3527 ∨ (¬ p4647))
    : p3527 ∨ (¬ p2911) ∨ (¬ p2156) ∨ p3399 ∨ (¬ p4521) ∨ (¬ p2901) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4647 := h105412;
    (Or.elim h93934 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123432 (p2187 p2274 p2307 p2608 p2962 p3367 p3641 p4384 p4521 : Prop)
    (h106167 : p4384)
    (h93941 : (¬ p2307) ∨ p2274 ∨ (¬ p2962) ∨ (¬ p2187) ∨ p2608 ∨ p3641 ∨ (¬ p4384) ∨ p3367 ∨ (¬ p4521))
    : p3367 ∨ p3641 ∨ p2608 ∨ (¬ p2962) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p2187) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4384 := h106167;
    (Or.elim h93941 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step123435 (p2481 p2509 p2630 p3005 p3171 p4811 : Prop)
    (h105633 : p4811)
    (h93965 : (¬ p2481) ∨ (¬ p3171) ∨ (¬ p4811) ∨ (¬ p3005) ∨ (¬ p2509) ∨ p2630)
    : (¬ p3171) ∨ (¬ p2509) ∨ p2630 ∨ (¬ p3005) ∨ (¬ p2481) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3171 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h93965 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step123436 (p2177 p2252 p2630 p2741 p3005 p3166 p3379 p3399 p3527 p4376 : Prop)
    (h106320 : p4376)
    (h93979 : p3379 ∨ (¬ p2252) ∨ (¬ p3005) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p2630 ∨ p2177 ∨ (¬ p4376) ∨ (¬ p2741) ∨ p3166)
    : p2630 ∨ (¬ p2252) ∨ (¬ p3005) ∨ p2177 ∨ p3379 ∨ (¬ p3399) ∨ (¬ p3527) ∨ p3166 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h93979 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u7 r8)))))))))))))))))))))

theorem step123443 (p2230 p2427 p2696 p3005 p3246 p3256 p4669 p4729 : Prop)
    (h105415 : p4669)
    (h105429 : p4729)
    (h94000 : (¬ p3005) ∨ (¬ p3256) ∨ p2230 ∨ p2427 ∨ (¬ p2696) ∨ (¬ p4729) ∨ (¬ p4669) ∨ p3246)
    : (¬ p2696) ∨ (¬ p3005) ∨ p2427 ∨ p2230 ∨ p3246 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4669 := h105415;
    let u7 : p4729 := h105429;
    (Or.elim h94000 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step123444 (p2220 p2954 p3005 p3136 p4311 : Prop)
    (h106494 : p2954)
    (h94001 : (¬ p4311) ∨ (¬ p3005) ∨ p3136 ∨ (¬ p2954) ∨ p2220)
    : p3136 ∨ p2220 ∨ (¬ p3005) ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h94001 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step123445 (p2230 p2696 p2982 p3005 p4009 p4322 p4729 p5119 : Prop)
    (h105429 : p4729)
    (h94005 : (¬ p4322) ∨ (¬ p4009) ∨ (¬ p2696) ∨ p2230 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p5119) ∨ p2982)
    : (¬ p4009) ∨ (¬ p2696) ∨ (¬ p5119) ∨ p2982 ∨ (¬ p3005) ∨ p2230 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    (Or.elim h94005 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step123451 (p2417 p2696 p2761 p3005 p3389 p4009 p4729 p5119 : Prop)
    (h105429 : p4729)
    (h94016 : p2761 ∨ (¬ p4009) ∨ (¬ p4729) ∨ p3389 ∨ p2417 ∨ (¬ p5119) ∨ (¬ p3005) ∨ (¬ p2696))
    : (¬ p4009) ∨ (¬ p2696) ∨ p2417 ∨ (¬ p5119) ∨ (¬ p3005) ∨ p2761 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    (Or.elim h94016 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step123456 (p2230 p2274 p2563 p2685 p3005 p3166 p3366 p3519 p4236 p4361 p4376 : Prop)
    (h106320 : p4376)
    (h105382 : p4361)
    (h94027 : p2685 ∨ p3166 ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p2563) ∨ (¬ p4361) ∨ (¬ p4236) ∨ (¬ p2274) ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p4236) ∨ (¬ p2563) ∨ p3166 ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p3366) ∨ p2685 ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p4361 := h105382;
    (Or.elim h94027 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step123457 (p2230 p2563 p2696 p3005 p3125 p3256 p4604 p4729 : Prop)
    (h106293 : p4604)
    (h105429 : p4729)
    (h94029 : (¬ p3005) ∨ p3125 ∨ p2563 ∨ (¬ p4729) ∨ p2230 ∨ (¬ p4604) ∨ (¬ p3256) ∨ (¬ p2696))
    : (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ p2563 ∨ p2230 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4604 := h106293;
    let u7 : p4729 := h105429;
    (Or.elim h94029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step123459 (p2187 p2230 p2563 p2608 p2737 p3005 p4771 p5193 : Prop)
    (h105488 : p5193)
    (h94031 : (¬ p3005) ∨ (¬ p2608) ∨ p2230 ∨ (¬ p2737) ∨ p2187 ∨ p2563 ∨ (¬ p5193) ∨ (¬ p4771))
    : p2230 ∨ p2563 ∨ (¬ p2737) ∨ (¬ p2608) ∨ (¬ p4771) ∨ p2187 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h94031 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step123464 (p2352 p2363 p2573 p2696 p3005 p4009 p4729 p5122 : Prop)
    (h105483 : p5122)
    (h105429 : p4729)
    (h94044 : (¬ p4009) ∨ p2363 ∨ p2352 ∨ (¬ p5122) ∨ p2573 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p2696))
    : (¬ p4009) ∨ (¬ p2696) ∨ (¬ p3005) ∨ p2352 ∨ p2573 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5122 := h105483;
    let u7 : p4729 := h105429;
    (Or.elim h94044 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step123465 (p2598 p3005 p3166 p4236 p4752 : Prop)
    (h105434 : p4752)
    (h94047 : (¬ p4236) ∨ p3166 ∨ (¬ p2598) ∨ (¬ p3005) ∨ (¬ p4752))
    : p3166 ∨ (¬ p3005) ∨ (¬ p2598) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4752 := h105434;
    (Or.elim h94047 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123466 (p2331 p2373 p2427 p2797 p3005 p3051 p3904 p4117 p4729 p5063 : Prop)
    (h105474 : p5063)
    (h105429 : p4729)
    (h94053 : p2797 ∨ (¬ p3005) ∨ (¬ p5063) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p2427) ∨ (¬ p4729) ∨ p3051 ∨ p2373)
    : p2373 ∨ p3051 ∨ (¬ p3904) ∨ p2797 ∨ (¬ p4117) ∨ (¬ p2427) ∨ (¬ p3005) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5063 := h105474;
    let u9 : p4729 := h105429;
    (Or.elim h94053 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u0 r8)))))))))))))))))))))

theorem step123472 (p2177 p2230 p2373 p3367 p3425 p3527 p3576 p3759 p4119 p4556 : Prop)
    (h105399 : p4556)
    (h94092 : (¬ p3759) ∨ p3527 ∨ (¬ p4556) ∨ (¬ p3425) ∨ (¬ p2373) ∨ (¬ p3576) ∨ (¬ p3367) ∨ (¬ p2230) ∨ (¬ p2177) ∨ (¬ p4119))
    : (¬ p3367) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p3425) ∨ (¬ p2373) ∨ (¬ p2230) ∨ (¬ p4119) ∨ (¬ p2177) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4556 := h105399;
    (Or.elim h94092 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step123474 (p2156 p2187 p2249 p2459 p2951 p2992 p3073 p3166 p4133 p4288 : Prop)
    (h105712 : p4133)
    (h106513 : p2249)
    (h94096 : (¬ p4288) ∨ (¬ p2156) ∨ p3166 ∨ p3073 ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2249))
    : p3073 ∨ p3166 ∨ (¬ p2951) ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p2992) ∨ (¬ p2156) ∨ (¬ p4288) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : p2249 := h106513;
    (Or.elim h94096 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step123479 (p2470 p2528 p2630 p2656 p2717 p2807 p4325 p5118 p5558 : Prop)
    (h105482 : p5118)
    (h94122 : (¬ p5558) ∨ p2807 ∨ (¬ p5118) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p4325) ∨ p2717)
    : (¬ p4325) ∨ p2717 ∨ (¬ p2630) ∨ (¬ p2528) ∨ p2807 ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5118 := h105482;
    (Or.elim h94122 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step123480 (p2608 p2911 p3073 p3389 p3449 p3519 p3941 p4376 p5122 : Prop)
    (h106320 : p4376)
    (h105483 : p5122)
    (h94123 : (¬ p3941) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p3389) ∨ p3073 ∨ p3449 ∨ (¬ p5122) ∨ (¬ p3519) ∨ (¬ p2911))
    : (¬ p3941) ∨ (¬ p3519) ∨ p3073 ∨ (¬ p3389) ∨ p3449 ∨ (¬ p2608) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p5122 := h105483;
    (Or.elim h94123 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step123487 (p2284 p2685 p3136 p3699 p4555 : Prop)
    (h105542 : p4555)
    (h94171 : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p4555) ∨ p2685 ∨ (¬ p3699))
    : (¬ p3136) ∨ p2685 ∨ (¬ p3699) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h94171 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123493 (p2241 p2744 p3998 p4436 p5242 p5693 : Prop)
    (h106503 : p2744)
    (h94192 : (¬ p5693) ∨ (¬ p3998) ∨ p2241 ∨ (¬ p4436) ∨ (¬ p5242) ∨ (¬ p2744))
    : (¬ p5242) ∨ (¬ p5693) ∨ (¬ p3998) ∨ p2241 ∨ (¬ p4436) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5242 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2744 := h106503;
    (Or.elim h94192 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123494 (p3379 p3998 p4376 p4492 p4874 p5242 p5693 : Prop)
    (h106320 : p4376)
    (h94194 : (¬ p5693) ∨ (¬ p3998) ∨ (¬ p5242) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874))
    : (¬ p4492) ∨ (¬ p5693) ∨ (¬ p4874) ∨ (¬ p5242) ∨ p3379 ∨ (¬ p3998) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4492 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4376 := h106320;
    (Or.elim h94194 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step123497 (p2246 p2264 p2459 p2744 p2807 p3379 p3449 p4257 p5118 p5693 : Prop)
    (h106503 : p2744)
    (h105482 : p5118)
    (h94209 : (¬ p5693) ∨ p3449 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2459) ∨ (¬ p5118) ∨ (¬ p4257) ∨ (¬ p2264) ∨ (¬ p3379))
    : (¬ p5693) ∨ (¬ p4257) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p3379) ∨ (¬ p2459) ∨ (¬ p2246) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p5118 := h105482;
    (Or.elim h94209 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step123500 (p2246 p2608 p2744 p2946 p3115 p3449 p3680 p5123 p5693 : Prop)
    (h106503 : p2744)
    (h94222 : (¬ p5693) ∨ (¬ p2246) ∨ (¬ p3115) ∨ (¬ p2946) ∨ p3449 ∨ (¬ p5123) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3680))
    : (¬ p3680) ∨ p3449 ∨ (¬ p5693) ∨ (¬ p5123) ∨ (¬ p3115) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h94222 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step123501 (p2482 p3449 p3998 p5190 p5693 : Prop)
    (h105487 : p5190)
    (h94223 : (¬ p5693) ∨ (¬ p3998) ∨ p3449 ∨ (¬ p5190) ∨ (¬ p2482))
    : (¬ p5693) ∨ p3449 ∨ (¬ p2482) ∨ (¬ p3998) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5190 := h105487;
    (Or.elim h94223 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123502 (p2241 p2598 p2750 p2753 p3276 p3333 p3449 p5123 p5693 : Prop)
    (h106345 : p2750)
    (h94224 : p3449 ∨ (¬ p5693) ∨ (¬ p3333) ∨ (¬ p2750) ∨ (¬ p2598) ∨ (¬ p5123) ∨ (¬ p3276) ∨ (¬ p2241) ∨ (¬ p2753))
    : (¬ p3276) ∨ (¬ p5693) ∨ (¬ p2241) ∨ p3449 ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p2598) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    (Or.elim h94224 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step123506 (p2528 p2651 p2761 p2778 p3083 p3654 p3670 p4669 p4786 p5269 : Prop)
    (h105415 : p4669)
    (h106425 : p4786)
    (h94241 : p3670 ∨ (¬ p5269) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p2761) ∨ (¬ p2528) ∨ (¬ p3083) ∨ p3654 ∨ (¬ p2651) ∨ (¬ p2778))
    : (¬ p5269) ∨ (¬ p2778) ∨ (¬ p2528) ∨ (¬ p2761) ∨ p3654 ∨ p3670 ∨ (¬ p3083) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5269 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    let u9 : p4786 := h106425;
    (Or.elim h94241 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step123507 (p2246 p2417 p2437 p2651 p2744 p3266 p3599 p3670 p3950 : Prop)
    (h106503 : p2744)
    (h94243 : p3670 ∨ (¬ p3266) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p2437) ∨ p3599 ∨ (¬ p3950) ∨ (¬ p2246) ∨ (¬ p2417))
    : p3670 ∨ p3599 ∨ (¬ p2437) ∨ (¬ p2417) ∨ (¬ p3266) ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h94243 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step123515 (p2248 p2437 p2608 p2651 p3599 p3670 p3868 p4826 : Prop)
    (h105365 : p2248)
    (h105444 : p4826)
    (h94292 : p3599 ∨ p3670 ∨ (¬ p4826) ∨ p2608 ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868))
    : (¬ p3868) ∨ p3599 ∨ (¬ p2437) ∨ p2608 ∨ (¬ p2651) ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4826 := h105444;
    (Or.elim h94292 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step123517 (p2352 p2573 p2608 p3599 p3670 p3979 p5119 p5190 : Prop)
    (h105487 : p5190)
    (h94297 : p3599 ∨ p3670 ∨ (¬ p2352) ∨ (¬ p2573) ∨ p2608 ∨ (¬ p5190) ∨ (¬ p5119) ∨ (¬ p3979))
    : (¬ p3979) ∨ p3670 ∨ (¬ p2352) ∨ p2608 ∨ (¬ p2573) ∨ p3599 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h94297 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step123520 (p2254 p2274 p2295 p2470 p2493 p2509 p2946 p3958 p4079 p4153 : Prop)
    (h105378 : p3958)
    (h105366 : p2254)
    (h94325 : (¬ p2509) ∨ (¬ p2470) ∨ (¬ p2274) ∨ (¬ p4153) ∨ (¬ p3958) ∨ (¬ p2254) ∨ p2946 ∨ p2295 ∨ (¬ p2493) ∨ (¬ p4079))
    : (¬ p2509) ∨ (¬ p4153) ∨ (¬ p2470) ∨ p2295 ∨ p2946 ∨ (¬ p2493) ∨ (¬ p2274) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3958 := h105378;
    let u9 : p2254 := h105366;
    (Or.elim h94325 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step123522 (p2363 p2383 p2510 p2528 p2581 : Prop)
    (h105371 : p2581)
    (h94332 : (¬ p2528) ∨ p2363 ∨ (¬ p2510) ∨ p2383 ∨ (¬ p2581))
    : p2383 ∨ (¬ p2528) ∨ p2363 ∨ (¬ p2510) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2581 := h105371;
    (Or.elim h94332 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123524 (p2417 p2449 p3096 p3156 p3920 p4386 p4509 : Prop)
    (h105392 : p4509)
    (h94342 : (¬ p2417) ∨ (¬ p3920) ∨ p2449 ∨ (¬ p4386) ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p3156))
    : (¬ p3920) ∨ (¬ p4386) ∨ (¬ p3156) ∨ (¬ p3096) ∨ p2449 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3920 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4509 := h105392;
    (Or.elim h94342 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step123525 (p2284 p2449 p3246 p4386 p4555 : Prop)
    (h105542 : p4555)
    (h94344 : (¬ p3246) ∨ p2449 ∨ (¬ p4555) ∨ (¬ p2284) ∨ (¬ p4386))
    : (¬ p4386) ∨ (¬ p2284) ∨ (¬ p3246) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h94344 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123526 (p2264 p2284 p2341 p3691 p4386 p4555 : Prop)
    (h105542 : p4555)
    (h94346 : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p2284) ∨ p2264 ∨ (¬ p4555))
    : (¬ p2341) ∨ (¬ p4386) ∨ (¬ p2284) ∨ (¬ p3691) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h94346 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123527 (p2264 p2341 p2573 p4241 p4386 p4715 p5201 : Prop)
    (h105423 : p4715)
    (h94347 : (¬ p2341) ∨ (¬ p4386) ∨ (¬ p4241) ∨ p2264 ∨ (¬ p5201) ∨ p2573 ∨ (¬ p4715))
    : (¬ p2341) ∨ p2573 ∨ p2264 ∨ (¬ p4386) ∨ (¬ p5201) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4715 := h105423;
    (Or.elim h94347 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step123528 (p2220 p2954 p2992 p3189 p4311 : Prop)
    (h106494 : p2954)
    (h94351 : (¬ p4311) ∨ (¬ p3189) ∨ (¬ p2954) ∨ p2220 ∨ p2992)
    : p2220 ∨ (¬ p4311) ∨ (¬ p3189) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h94351 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step123533 (p2241 p2352 p2573 p3506 p3842 p5123 p5193 p5580 : Prop)
    (h105488 : p5193)
    (h94388 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p2241) ∨ p2352 ∨ (¬ p5193) ∨ p2573 ∨ (¬ p3506) ∨ (¬ p3842))
    : (¬ p3506) ∨ (¬ p3842) ∨ (¬ p5123) ∨ p2573 ∨ p2352 ∨ (¬ p5580) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h94388 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step123534 (p2241 p2911 p3389 p3506 p3842 p5123 p5193 p5558 : Prop)
    (h105488 : p5193)
    (h94389 : (¬ p5558) ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2911 ∨ (¬ p3842) ∨ (¬ p5123) ∨ p3389 ∨ (¬ p5193))
    : (¬ p3506) ∨ (¬ p5558) ∨ (¬ p5123) ∨ p3389 ∨ p2911 ∨ (¬ p3842) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h94389 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123535 (p2230 p2241 p2373 p3506 p3842 p5123 p5193 p5568 : Prop)
    (h105488 : p5193)
    (h94403 : (¬ p5568) ∨ (¬ p3506) ∨ p2230 ∨ (¬ p3842) ∨ p2373 ∨ (¬ p5123) ∨ (¬ p2241) ∨ (¬ p5193))
    : (¬ p3506) ∨ (¬ p3842) ∨ (¬ p5568) ∨ p2373 ∨ p2230 ∨ (¬ p2241) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h94403 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123537 (p2241 p2553 p2573 p3506 p3842 p4260 p4831 p5193 : Prop)
    (h105488 : p5193)
    (h105445 : p4831)
    (h94406 : (¬ p4260) ∨ (¬ p3506) ∨ p2573 ∨ (¬ p2241) ∨ (¬ p5193) ∨ p2553 ∨ (¬ p4831) ∨ (¬ p3842))
    : (¬ p3506) ∨ (¬ p3842) ∨ (¬ p2241) ∨ p2573 ∨ p2553 ∨ (¬ p4260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4831 := h105445;
    (Or.elim h94406 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step123538 (p2807 p3246 p3286 p4280 p4656 : Prop)
    (h105599 : p4280)
    (h94419 : p3286 ∨ (¬ p4656) ∨ (¬ p4280) ∨ (¬ p3246) ∨ (¬ p2807))
    : (¬ p2807) ∨ p3286 ∨ (¬ p3246) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    (Or.elim h94419 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123539 (p2264 p2807 p3286 p4656 p4666 : Prop)
    (h105658 : p4666)
    (h94421 : (¬ p4656) ∨ p3286 ∨ (¬ p4666) ∨ (¬ p2807) ∨ (¬ p2264))
    : (¬ p2807) ∨ p3286 ∨ (¬ p2264) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h94421 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123544 (p2449 p2630 p3434 p4652 p4781 : Prop)
    (h105413 : p4652)
    (h94442 : (¬ p3434) ∨ p2449 ∨ (¬ p4781) ∨ p2630 ∨ (¬ p4652))
    : (¬ p3434) ∨ p2630 ∨ (¬ p4781) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4652 := h105413;
    (Or.elim h94442 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123548 (p2598 p3434 p3516 p3820 p4752 p4781 : Prop)
    (h105434 : p4752)
    (h94454 : (¬ p3434) ∨ p3516 ∨ (¬ p2598) ∨ (¬ p4781) ∨ (¬ p3820) ∨ (¬ p4752))
    : (¬ p3434) ∨ (¬ p3820) ∨ (¬ p2598) ∨ (¬ p4781) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4752 := h105434;
    (Or.elim h94454 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123553 (p2307 p2608 p3309 p4512 p4877 p5020 : Prop)
    (h105451 : p4877)
    (h94500 : p2608 ∨ p3309 ∨ (¬ p5020) ∨ (¬ p4877) ∨ (¬ p4512) ∨ (¬ p2307))
    : (¬ p2307) ∨ (¬ p5020) ∨ (¬ p4512) ∨ p2608 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4877 := h105451;
    (Or.elim h94500 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123554 (p2166 p2274 p3309 p4509 p4512 : Prop)
    (h105392 : p4509)
    (h94501 : p3309 ∨ (¬ p2274) ∨ (¬ p2166) ∨ (¬ p4512) ∨ (¬ p4509))
    : (¬ p4512) ∨ (¬ p2166) ∨ (¬ p2274) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h94501 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123555 (p2166 p2307 p3309 p3743 p4509 p4512 : Prop)
    (h105392 : p4509)
    (h94502 : (¬ p2307) ∨ p3309 ∨ (¬ p3743) ∨ (¬ p4509) ∨ (¬ p4512) ∨ (¬ p2166))
    : (¬ p4512) ∨ (¬ p3743) ∨ (¬ p2307) ∨ p3309 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    (Or.elim h94502 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step123557 (p2891 p3319 p3654 p3743 p4512 p4558 : Prop)
    (h105400 : p4558)
    (h94514 : (¬ p3654) ∨ p3319 ∨ (¬ p4512) ∨ (¬ p2891) ∨ (¬ p3743) ∨ (¬ p4558))
    : (¬ p4512) ∨ (¬ p3743) ∨ (¬ p2891) ∨ (¬ p3654) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h94514 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123563 (p2274 p2972 p3309 p4512 p5046 : Prop)
    (h105472 : p5046)
    (h94526 : p3309 ∨ (¬ p2274) ∨ (¬ p2972) ∨ (¬ p4512) ∨ (¬ p5046))
    : (¬ p4512) ∨ (¬ p2972) ∨ p3309 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    (Or.elim h94526 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123564 (p3016 p3319 p3564 p4202 p4512 p4811 : Prop)
    (h105633 : p4811)
    (h94527 : (¬ p3564) ∨ p3319 ∨ (¬ p4512) ∨ (¬ p3016) ∨ (¬ p4811) ∨ (¬ p4202))
    : (¬ p4512) ∨ (¬ p3564) ∨ (¬ p3016) ∨ (¬ p4202) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h94527 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step123568 (p2753 p3093 p3276 p3286 p3399 p3506 p3631 p4117 p4512 p4638 p4877 : Prop)
    (h105451 : p4877)
    (h105409 : p4638)
    (h94536 : p3276 ∨ p3399 ∨ (¬ p4877) ∨ (¬ p3093) ∨ p3631 ∨ (¬ p4512) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p4638))
    : (¬ p3506) ∨ p3399 ∨ (¬ p3093) ∨ (¬ p4512) ∨ (¬ p3286) ∨ p3631 ∨ (¬ p2753) ∨ (¬ p4117) ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    let u10 : p4638 := h105409;
    (Or.elim h94536 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step123570 (p2901 p3125 p3319 p4282 p4512 p4558 : Prop)
    (h105400 : p4558)
    (h94539 : (¬ p3125) ∨ (¬ p4282) ∨ (¬ p4558) ∨ (¬ p2901) ∨ p3319 ∨ (¬ p4512))
    : (¬ p4282) ∨ p3319 ∨ (¬ p3125) ∨ (¬ p4512) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4282 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h94539 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step123574 (p2315 p2341 p2363 p2459 p3325 : Prop)
    (h105368 : p2315)
    (h94545 : p2341 ∨ (¬ p3325) ∨ (¬ p2315) ∨ (¬ p2363) ∨ p2459)
    : p2341 ∨ p2459 ∨ (¬ p3325) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2315 := h105368;
    (Or.elim h94545 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step123579 (p2264 p2341 p2427 p3691 p4386 p4702 : Prop)
    (h106079 : p4702)
    (h94577 : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p4702) ∨ p2264 ∨ (¬ p4386) ∨ (¬ p2427))
    : (¬ p2341) ∨ (¬ p3691) ∨ p2264 ∨ (¬ p2427) ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    (Or.elim h94577 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step123580 (p2341 p2441 p2901 p2911 p3691 p4705 : Prop)
    (h106238 : p4705)
    (h94579 : (¬ p2901) ∨ (¬ p3691) ∨ p2911 ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p4705))
    : (¬ p3691) ∨ (¬ p2341) ∨ (¬ p2901) ∨ p2911 ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3691 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h94579 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123588 (p2192 p2220 p2553 p2598 p3073 p3146 p3422 p4172 p4492 p4736 : Prop)
    (h105431 : p4736)
    (h94602 : p3422 ∨ (¬ p2220) ∨ p2553 ∨ (¬ p4736) ∨ (¬ p3146) ∨ (¬ p4492) ∨ (¬ p4172) ∨ (¬ p2192) ∨ p2598 ∨ p3073)
    : (¬ p4492) ∨ (¬ p2192) ∨ p2553 ∨ p3422 ∨ (¬ p4172) ∨ p3073 ∨ (¬ p2220) ∨ p2598 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4492 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4736 := h105431;
    (Or.elim h94602 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step123590 (p2510 p2528 p2891 p3073 p3096 p4492 p4558 : Prop)
    (h105400 : p4558)
    (h94609 : p3073 ∨ (¬ p4558) ∨ (¬ p2510) ∨ (¬ p4492) ∨ (¬ p2891) ∨ (¬ p2528) ∨ (¬ p3096))
    : (¬ p2510) ∨ (¬ p4492) ∨ (¬ p2891) ∨ (¬ p3096) ∨ p3073 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4558 := h105400;
    (Or.elim h94609 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step123595 (p2210 p2449 p2685 p2696 p2753 p3146 p3449 p3906 p3950 p4877 : Prop)
    (h105451 : p4877)
    (h94629 : (¬ p2449) ∨ p3146 ∨ (¬ p2753) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p3906) ∨ (¬ p2696) ∨ p3449 ∨ (¬ p3950) ∨ (¬ p4877))
    : p3449 ∨ (¬ p3906) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p2449) ∨ (¬ p3950) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    (Or.elim h94629 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step123598 (p2088 p2143 p2641 p2668 p2696 p2742 p2839 p3146 p3697 p4134 : Prop)
    (h105379 : p4134)
    (h94640 : (¬ p2668) ∨ (¬ p2742) ∨ (¬ p4134) ∨ p2839 ∨ (¬ p3146) ∨ p2088 ∨ (¬ p2696) ∨ (¬ p2143) ∨ (¬ p2641) ∨ (¬ p3697))
    : (¬ p2143) ∨ p2839 ∨ (¬ p2668) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p2641) ∨ p2088 ∨ (¬ p3697) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4134 := h105379;
    (Or.elim h94640 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step123599 (p2088 p2954 p3146 p3156 p3697 : Prop)
    (h106494 : p2954)
    (h94641 : p2088 ∨ (¬ p3146) ∨ (¬ p2954) ∨ (¬ p3697) ∨ (¬ p3156))
    : (¬ p3697) ∨ p2088 ∨ (¬ p3146) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3697 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h94641 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step123600 (p2088 p2373 p3146 p3697 p4533 : Prop)
    (h105394 : p4533)
    (h94644 : (¬ p3697) ∨ p2088 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p3146))
    : (¬ p3697) ∨ (¬ p2373) ∨ (¬ p3146) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3697 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h94644 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123603 (p2088 p2510 p2528 p3051 p3096 p3697 p4558 : Prop)
    (h105400 : p4558)
    (h94651 : (¬ p2510) ∨ (¬ p3697) ∨ p2088 ∨ (¬ p4558) ∨ (¬ p2528) ∨ (¬ p3096) ∨ (¬ p3051))
    : (¬ p3697) ∨ (¬ p2510) ∨ (¬ p3096) ∨ (¬ p2528) ∨ p2088 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3697 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4558 := h105400;
    (Or.elim h94651 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step123609 (p2668 p4228 p4503 p5558 p5584 : Prop)
    (h106530 : p4503)
    (h94690 : (¬ p4228) ∨ (¬ p5558) ∨ (¬ p5584) ∨ p2668 ∨ (¬ p4503))
    : (¬ p5584) ∨ (¬ p4228) ∨ p2668 ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    (Or.elim h94690 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123612 (p2166 p2220 p2331 p2950 p3948 p4116 p4975 : Prop)
    (h105464 : p4975)
    (h94754 : (¬ p4116) ∨ (¬ p2950) ∨ (¬ p3948) ∨ p2220 ∨ (¬ p2166) ∨ (¬ p2331) ∨ (¬ p4975))
    : (¬ p2950) ∨ p2220 ∨ (¬ p2331) ∨ (¬ p2166) ∨ (¬ p3948) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4975 := h105464;
    (Or.elim h94754 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step123615 (p2187 p2383 p3051 p4198 p4558 : Prop)
    (h105400 : p4558)
    (h94768 : (¬ p4558) ∨ (¬ p2187) ∨ (¬ p3051) ∨ p2383 ∨ (¬ p4198))
    : (¬ p4198) ∨ (¬ p3051) ∨ p2383 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h94768 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123625 (p2088 p2954 p3146 p3156 p4197 p4198 : Prop)
    (h106494 : p2954)
    (h94788 : p2088 ∨ (¬ p4197) ∨ (¬ p3156) ∨ (¬ p2954) ∨ (¬ p3146) ∨ (¬ p4198))
    : (¬ p4198) ∨ p2088 ∨ (¬ p3146) ∨ (¬ p4197) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2954 := h106494;
    (Or.elim h94788 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123630 (p2274 p2307 p2957 p3156 p4198 p4509 : Prop)
    (h105392 : p4509)
    (h94800 : (¬ p4198) ∨ (¬ p2274) ∨ (¬ p2957) ∨ (¬ p4509) ∨ p2307 ∨ (¬ p3156))
    : (¬ p2957) ∨ (¬ p4198) ∨ p2307 ∨ (¬ p3156) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    (Or.elim h94800 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step123633 (p2311 p2891 p3246 p3516 p4198 p4522 : Prop)
    (h105393 : p4522)
    (h94810 : p3516 ∨ (¬ p3246) ∨ (¬ p4198) ∨ (¬ p2311) ∨ (¬ p4522) ∨ (¬ p2891))
    : (¬ p2891) ∨ (¬ p4198) ∨ p3516 ∨ (¬ p2311) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4522 := h105393;
    (Or.elim h94810 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123639 (p2717 p3246 p3941 p4169 p4445 p5122 : Prop)
    (h105483 : p5122)
    (h94831 : p3246 ∨ (¬ p2717) ∨ (¬ p4169) ∨ (¬ p5122) ∨ (¬ p4445) ∨ (¬ p3941))
    : (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p2717) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5122 := h105483;
    (Or.elim h94831 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123640 (p4169 p4477 p4559 : Prop)
    (h105701 : p4559)
    (h22439 : (¬ p4169) ∨ p4477 ∨ (¬ p4559))
    : (¬ p4169) ∨ p4477 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4477) := (fun h => hn (Or.inr h));
    let u2 : p4559 := h105701;
    (Or.elim h22439 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step123642 (p2717 p2881 p2891 p4136 p4878 : Prop)
    (h105452 : p4878)
    (h94839 : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p4878) ∨ p2717 ∨ (¬ p4136))
    : p2717 ∨ (¬ p4136) ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    (Or.elim h94839 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step123646 (p2860 p3246 p3434 p4136 p4555 : Prop)
    (h105542 : p4555)
    (h94850 : (¬ p4136) ∨ p3434 ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4555))
    : (¬ p4136) ∨ (¬ p2860) ∨ p3434 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h94850 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123647 (p2136 p2860 p3051 p3425 p4136 p4555 : Prop)
    (h105542 : p4555)
    (h94851 : (¬ p4136) ∨ p3051 ∨ (¬ p4555) ∨ (¬ p2860) ∨ (¬ p2136) ∨ p3425)
    : p3425 ∨ p3051 ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p4136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h94851 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step123651 (p2619 p3246 p3434 p3872 p4136 p4509 : Prop)
    (h105392 : p4509)
    (h94860 : (¬ p2619) ∨ (¬ p3246) ∨ p3434 ∨ (¬ p4509) ∨ (¬ p3872) ∨ (¬ p4136))
    : p3434 ∨ (¬ p4136) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    (Or.elim h94860 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step123653 (p2427 p3246 p3434 p4136 p4882 : Prop)
    (h105453 : p4882)
    (h94870 : (¬ p3246) ∨ (¬ p4136) ∨ (¬ p2427) ∨ (¬ p4882) ∨ p3434)
    : (¬ p3246) ∨ (¬ p4136) ∨ (¬ p2427) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    (Or.elim h94870 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step123662 (p2383 p2437 p2668 p2962 p4109 p4194 p4646 : Prop)
    (h105534 : p4646)
    (h94895 : (¬ p2383) ∨ (¬ p4194) ∨ (¬ p4646) ∨ (¬ p4109) ∨ (¬ p2962) ∨ (¬ p2437) ∨ p2668)
    : (¬ p4194) ∨ (¬ p4109) ∨ (¬ p2962) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4194 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4646 := h105534;
    (Or.elim h94895 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u4 r5)))))))))))))))

theorem step123664 (p2352 p2573 p2665 p2668 p4194 : Prop)
    (h105373 : p2665)
    (h94897 : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ p2668 ∨ (¬ p4194))
    : (¬ p2573) ∨ (¬ p2352) ∨ p2668 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    (Or.elim h94897 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step123667 (p2295 p2440 p2553 p4194 p4715 : Prop)
    (h105423 : p4715)
    (h94902 : p2295 ∨ p2440 ∨ (¬ p4194) ∨ (¬ p4715) ∨ (¬ p2553))
    : (¬ p4194) ∨ p2440 ∨ (¬ p2553) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4194 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h94902 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123668 (p2177 p2264 p2307 p4067 p4584 : Prop)
    (h105406 : p4584)
    (h94903 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p4067) ∨ p2264 ∨ (¬ p4584))
    : (¬ p2307) ∨ (¬ p2177) ∨ p2264 ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4584 := h105406;
    (Or.elim h94903 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123670 (p2383 p2630 p2667 p2819 p4426 p4975 : Prop)
    (h105464 : p4975)
    (h94909 : (¬ p2819) ∨ p2383 ∨ (¬ p4426) ∨ (¬ p4975) ∨ p2630 ∨ (¬ p2667))
    : (¬ p2819) ∨ p2630 ∨ (¬ p2667) ∨ (¬ p4426) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h94909 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step123672 (p2122 p2295 p2641 p2745 p4426 : Prop)
    (h105523 : p2745)
    (h94916 : p2295 ∨ p2641 ∨ (¬ p2122) ∨ (¬ p4426) ∨ (¬ p2745))
    : (¬ p4426) ∨ (¬ p2122) ∨ p2641 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4426 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h94916 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123674 (p2248 p2331 p2509 p2528 p2797 p3379 p3755 p5109 : Prop)
    (h105365 : p2248)
    (h94937 : (¬ p3755) ∨ p2797 ∨ (¬ p5109) ∨ p2528 ∨ (¬ p2248) ∨ (¬ p2509) ∨ p3379 ∨ (¬ p2331))
    : (¬ p2509) ∨ (¬ p5109) ∨ p2528 ∨ (¬ p3755) ∨ p2797 ∨ (¬ p2331) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h94937 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step123684 (p2230 p2331 p2373 p2797 p3146 p3755 p4117 p4729 p5109 : Prop)
    (h105429 : p4729)
    (h94986 : (¬ p3755) ∨ p2797 ∨ p2230 ∨ (¬ p4729) ∨ p3146 ∨ (¬ p5109) ∨ (¬ p2331) ∨ (¬ p4117) ∨ p2373)
    : p2797 ∨ (¬ p3755) ∨ (¬ p5109) ∨ p2373 ∨ p2230 ∨ p3146 ∨ (¬ p4117) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    (Or.elim h94986 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step123685 (p2230 p2373 p2696 p3506 p3755 p4729 p5123 p5568 : Prop)
    (h105429 : p4729)
    (h95000 : (¬ p5568) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p2696) ∨ p2373 ∨ p2230 ∨ (¬ p4729))
    : (¬ p3506) ∨ (¬ p3755) ∨ p2373 ∨ (¬ p5568) ∨ (¬ p2696) ∨ p2230 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    (Or.elim h95000 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123688 (p2553 p2573 p2696 p3506 p3589 p3755 p4260 p4831 p5193 : Prop)
    (h105488 : p5193)
    (h105445 : p4831)
    (h95011 : (¬ p3506) ∨ (¬ p4260) ∨ p2573 ∨ (¬ p5193) ∨ (¬ p3589) ∨ (¬ p3755) ∨ p2553 ∨ (¬ p2696) ∨ (¬ p4831))
    : (¬ p3506) ∨ (¬ p3755) ∨ p2553 ∨ (¬ p2696) ∨ (¬ p4260) ∨ (¬ p3589) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p4831 := h105445;
    (Or.elim h95011 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step123691 (p2145 p2156 p2553 p2696 p3506 p3755 p4203 p4260 p4831 : Prop)
    (h105445 : p4831)
    (h95018 : (¬ p4260) ∨ (¬ p3506) ∨ p2156 ∨ (¬ p2145) ∨ (¬ p4831) ∨ (¬ p2696) ∨ (¬ p4203) ∨ p2553 ∨ (¬ p3755))
    : (¬ p3506) ∨ (¬ p3755) ∨ (¬ p2696) ∨ p2553 ∨ (¬ p4260) ∨ (¬ p4203) ∨ (¬ p2145) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4831 := h105445;
    (Or.elim h95018 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step123693 (p2230 p2427 p2608 p2737 p3246 p3755 p4658 p5193 : Prop)
    (h105488 : p5193)
    (h95024 : (¬ p3755) ∨ (¬ p2608) ∨ (¬ p4658) ∨ p3246 ∨ (¬ p2737) ∨ p2230 ∨ p2427 ∨ (¬ p5193))
    : (¬ p3755) ∨ (¬ p2737) ∨ p3246 ∨ p2427 ∨ (¬ p4658) ∨ (¬ p2608) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h95024 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123695 (p2230 p2373 p2685 p2807 p3146 p3755 p4117 p4729 p5109 : Prop)
    (h105429 : p4729)
    (h95040 : (¬ p5109) ∨ p3146 ∨ p2685 ∨ (¬ p2807) ∨ p2230 ∨ p2373 ∨ (¬ p4117) ∨ (¬ p3755) ∨ (¬ p4729))
    : (¬ p3755) ∨ p2685 ∨ (¬ p5109) ∨ (¬ p2807) ∨ (¬ p4117) ∨ p2230 ∨ p3146 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    (Or.elim h95040 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step123696 (p2307 p2352 p2553 p3005 p3286 p3366 p3755 p4236 p4774 p4866 p5016 : Prop)
    (h106063 : p4866)
    (h95049 : (¬ p3755) ∨ (¬ p5016) ∨ (¬ p4866) ∨ p3286 ∨ p3005 ∨ p2553 ∨ (¬ p2352) ∨ (¬ p4774) ∨ (¬ p2307) ∨ (¬ p3366) ∨ (¬ p4236))
    : p3005 ∨ (¬ p4236) ∨ (¬ p3755) ∨ p2553 ∨ (¬ p4774) ∨ (¬ p2352) ∨ (¬ p2307) ∨ p3286 ∨ (¬ p5016) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4866 := h106063;
    (Or.elim h95049 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step123698 (p2630 p2651 p2753 p3204 p3266 p3461 p3654 p3755 p4117 p4512 p4877 p5109 : Prop)
    (h105451 : p4877)
    (h95054 : (¬ p3266) ∨ (¬ p4512) ∨ p3461 ∨ (¬ p5109) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p3755) ∨ p2630 ∨ (¬ p2651) ∨ (¬ p3204) ∨ (¬ p4117) ∨ p3654)
    : (¬ p4117) ∨ (¬ p4512) ∨ (¬ p5109) ∨ (¬ p3204) ∨ p3461 ∨ p2630 ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p2651) ∨ (¬ p2753) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4877 := h105451;
    (Or.elim h95054 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u0))) (fun r10 => (False.elim (u10 r10)))))))))))))))))))))))))

theorem step123701 (p2373 p3998 p4238 p4539 p5568 : Prop)
    (h105395 : p4539)
    (h95078 : (¬ p3998) ∨ (¬ p5568) ∨ p2373 ∨ (¬ p4238) ∨ (¬ p4539))
    : (¬ p5568) ∨ (¬ p4238) ∨ (¬ p3998) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4539 := h105395;
    (Or.elim h95078 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123702 (p2145 p2264 p2459 p3051 p3276 p3355 p3362 p3461 p4330 p4333 : Prop)
    (h106329 : p4330)
    (h95087 : (¬ p3276) ∨ p3461 ∨ p2264 ∨ (¬ p3362) ∨ (¬ p2145) ∨ (¬ p4330) ∨ p3051 ∨ (¬ p3355) ∨ p2459 ∨ (¬ p4333))
    : (¬ p3276) ∨ p3051 ∨ (¬ p4333) ∨ p2459 ∨ p2264 ∨ p3461 ∨ (¬ p3362) ∨ (¬ p3355) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4330 := h106329;
    (Or.elim h95087 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step123706 (p2341 p2573 p2911 p3741 p4717 p5197 : Prop)
    (h105424 : p4717)
    (h95097 : (¬ p2911) ∨ p2341 ∨ (¬ p2573) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197))
    : (¬ p5197) ∨ (¬ p2911) ∨ p2341 ∨ (¬ p3741) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5197 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h95097 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step123715 (p2136 p2156 p2246 p2363 p2437 p2663 p2744 p3083 p3146 p3366 p3389 p3988 p4596 : Prop)
    (h106503 : p2744)
    (h95124 : (¬ p3389) ∨ p2437 ∨ (¬ p2363) ∨ p3146 ∨ (¬ p3083) ∨ p2156 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4596) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p3988) ∨ (¬ p2136))
    : p2156 ∨ (¬ p3389) ∨ p3146 ∨ (¬ p2663) ∨ (¬ p2136) ∨ p2437 ∨ (¬ p3083) ∨ (¬ p2363) ∨ (¬ p3988) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2744 := h106503;
    (Or.elim h95124 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u4)))))))))))))))))))))))))))

theorem step123719 (p2136 p2220 p2598 p2619 p4313 p4752 : Prop)
    (h105434 : p4752)
    (h95135 : (¬ p2136) ∨ (¬ p4313) ∨ p2220 ∨ (¬ p4752) ∨ (¬ p2598) ∨ (¬ p2619))
    : p2220 ∨ (¬ p4313) ∨ (¬ p2598) ∨ (¬ p2136) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4752 := h105434;
    (Or.elim h95135 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step123725 (p2192 p2255 p2946 p3125 p3266 p3297 p3412 p3773 p3848 p4330 : Prop)
    (h105367 : p2255)
    (h106329 : p4330)
    (h51687 : (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3297) ∨ (¬ p3412) ∨ (¬ p3773) ∨ (¬ p3848) ∨ (¬ p4330))
    : (¬ p3412) ∨ (¬ p2192) ∨ (¬ p3773) ∨ (¬ p3297) ∨ (¬ p2946) ∨ (¬ p3266) ∨ (¬ p3125) ∨ (¬ p3848) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3412 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4330 := h106329;
    (Or.elim h51687 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step123726 (p2156 p2177 p2241 p2274 p2727 p3083 p4420 : Prop)
    (h105707 : p4420)
    (h95161 : p2274 ∨ (¬ p3083) ∨ p2156 ∨ p2177 ∨ (¬ p2727) ∨ (¬ p4420) ∨ (¬ p2241))
    : (¬ p3083) ∨ p2156 ∨ (¬ p2727) ∨ (¬ p2241) ∨ p2274 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4420 := h105707;
    (Or.elim h95161 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step123734 (p2088 p2241 p2744 p3073 p4436 p5242 : Prop)
    (h106503 : p2744)
    (h95196 : p3073 ∨ p2241 ∨ (¬ p2744) ∨ (¬ p4436) ∨ (¬ p2088) ∨ (¬ p5242))
    : p3073 ∨ (¬ p4436) ∨ (¬ p2088) ∨ p2241 ∨ (¬ p5242) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2744 := h106503;
    (Or.elim h95196 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step123735 (p2156 p2274 p2396 p2608 p3370 p3399 p3527 p4377 p4668 : Prop)
    (h105414 : p4668)
    (h106170 : p4377)
    (h95200 : p3399 ∨ (¬ p2396) ∨ (¬ p4668) ∨ (¬ p3370) ∨ (¬ p2274) ∨ p3527 ∨ (¬ p4377) ∨ (¬ p2608) ∨ (¬ p2156))
    : (¬ p3370) ∨ p3399 ∨ (¬ p2396) ∨ (¬ p2156) ∨ p3527 ∨ (¬ p2608) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4668 := h105414;
    let u8 : p4377 := h106170;
    (Or.elim h95200 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step123736 (p2608 p2972 p3369 p4032 p4377 : Prop)
    (h106170 : p4377)
    (h63822 : (¬ p2608) ∨ (¬ p2972) ∨ (¬ p3369) ∨ (¬ p4032) ∨ (¬ p4377))
    : (¬ p3369) ∨ (¬ p4032) ∨ (¬ p2972) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4377 := h106170;
    (Or.elim h63822 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123737 (p2220 p2459 p2509 p2608 p3146 p3370 p3379 p4377 p4438 : Prop)
    (h106170 : p4377)
    (h95201 : (¬ p3370) ∨ (¬ p3146) ∨ (¬ p2608) ∨ (¬ p2220) ∨ p2459 ∨ (¬ p4438) ∨ p3379 ∨ (¬ p4377) ∨ (¬ p2509))
    : (¬ p3146) ∨ p3379 ∨ (¬ p4438) ∨ (¬ p3370) ∨ (¬ p2220) ∨ (¬ p2509) ∨ p2459 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    (Or.elim h95201 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step123739 (p4373 p4752 p5370 : Prop)
    (h105434 : p4752)
    (h26298 : (¬ p4373) ∨ (¬ p4752) ∨ p5370)
    : (¬ p4373) ∨ p5370 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5370) := (fun h => hn (Or.inr h));
    let u2 : p4752 := h105434;
    (Or.elim h26298 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step123742 (p2470 p2528 p2685 p2753 p2807 p3005 p3146 p3347 p4117 p5063 : Prop)
    (h105474 : p5063)
    (h95216 : (¬ p3005) ∨ (¬ p2753) ∨ (¬ p2807) ∨ p2528 ∨ (¬ p4117) ∨ p2470 ∨ (¬ p3146) ∨ p2685 ∨ (¬ p5063) ∨ (¬ p3347))
    : (¬ p3005) ∨ p2685 ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p4117) ∨ p2470 ∨ (¬ p2753) ∨ (¬ p3146) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5063 := h105474;
    (Or.elim h95216 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step123744 (p2946 p2972 p3286 p4040 p4960 : Prop)
    (h106209 : p4960)
    (h95221 : (¬ p4040) ∨ p3286 ∨ (¬ p4960) ∨ (¬ p2972) ∨ (¬ p2946))
    : (¬ p4040) ∨ p3286 ∨ (¬ p2972) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h95221 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step123750 (p2132 p2187 p2459 p2509 p2528 p2753 p2860 p4133 : Prop)
    (h105712 : p4133)
    (h95242 : (¬ p2753) ∨ (¬ p2509) ∨ (¬ p2860) ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p4133) ∨ p2528 ∨ (¬ p2132))
    : (¬ p2132) ∨ (¬ p2753) ∨ p2528 ∨ (¬ p2459) ∨ (¬ p2860) ∨ (¬ p2509) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    (Or.elim h95242 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step123751 (p2098 p2241 p2459 p2641 p2668 p3609 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h95243 : p3609 ∨ (¬ p2668) ∨ p2098 ∨ (¬ p4133) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p4736) ∨ (¬ p2459))
    : (¬ p2241) ∨ p2098 ∨ p3609 ∨ (¬ p2641) ∨ (¬ p2459) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4133 := h105712;
    (Or.elim h95243 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step123752 (p2459 p2470 p2528 p2608 p3063 p3093 p3347 p4133 : Prop)
    (h105712 : p4133)
    (h95244 : (¬ p3063) ∨ p2608 ∨ (¬ p4133) ∨ (¬ p3347) ∨ p2528 ∨ (¬ p3093) ∨ (¬ p2459) ∨ p2470)
    : (¬ p3063) ∨ p2528 ∨ (¬ p2459) ∨ (¬ p3347) ∨ (¬ p3093) ∨ p2608 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    (Or.elim h95244 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u6 r6)))))))))))))))))

theorem step123754 (p2860 p4019 p4509 p4744 p5568 : Prop)
    (h105392 : p4509)
    (h95252 : (¬ p5568) ∨ (¬ p4019) ∨ (¬ p4744) ∨ (¬ p4509) ∨ p2860)
    : (¬ p4019) ∨ (¬ p4744) ∨ p2860 ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h95252 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step123756 (p2230 p2427 p2696 p3005 p3246 p3256 p3366 p3519 p3950 p4376 : Prop)
    (h106320 : p4376)
    (h95263 : p3005 ∨ (¬ p2230) ∨ (¬ p3366) ∨ (¬ p2427) ∨ p2696 ∨ (¬ p3246) ∨ (¬ p3519) ∨ p3256 ∨ (¬ p3950) ∨ (¬ p4376))
    : (¬ p3246) ∨ (¬ p2427) ∨ (¬ p3519) ∨ p3005 ∨ p2696 ∨ (¬ p3366) ∨ (¬ p3950) ∨ p3256 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h95263 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step123757 (p2573 p2696 p3005 p3366 p3461 p3519 p3564 p4376 p5123 p5600 : Prop)
    (h106320 : p4376)
    (h95265 : p3005 ∨ (¬ p3461) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3564) ∨ (¬ p4376) ∨ p2696 ∨ (¬ p3519) ∨ (¬ p5600) ∨ (¬ p5123))
    : (¬ p2573) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3366) ∨ p3005 ∨ (¬ p5600) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h95265 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step123761 (p2493 p2584 p3564 p3654 p5194 : Prop)
    (h105489 : p5194)
    (h95330 : (¬ p3654) ∨ p3564 ∨ p2493 ∨ (¬ p5194) ∨ (¬ p2584))
    : (¬ p2584) ∨ (¬ p3654) ∨ p2493 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5194 := h105489;
    (Or.elim h95330 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123763 (p2156 p2406 p2563 p4399 p5194 : Prop)
    (h105489 : p5194)
    (h95331 : (¬ p2156) ∨ (¬ p4399) ∨ (¬ p5194) ∨ p2406 ∨ p2563)
    : (¬ p2156) ∨ (¬ p4399) ∨ p2563 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5194 := h105489;
    (Or.elim h95331 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step123764 (p2254 p2459 p2651 p3016 p3399 p3527 p3564 p4604 : Prop)
    (h105366 : p2254)
    (h106293 : p4604)
    (h95335 : (¬ p3527) ∨ p3564 ∨ p3016 ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p3399) ∨ p2651 ∨ (¬ p2254))
    : p3016 ∨ p2651 ∨ (¬ p3527) ∨ p3564 ∨ (¬ p2459) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4604 := h106293;
    (Or.elim h95335 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123765 (p2341 p2459 p2493 p2598 p2707 p3564 p3577 p4030 p4604 : Prop)
    (h106293 : p4604)
    (h95339 : (¬ p2707) ∨ (¬ p4030) ∨ (¬ p2459) ∨ p3564 ∨ p2598 ∨ (¬ p2341) ∨ (¬ p3577) ∨ p2493 ∨ (¬ p4604))
    : (¬ p3577) ∨ (¬ p2707) ∨ p2493 ∨ p2598 ∨ p3564 ∨ (¬ p2341) ∨ (¬ p4030) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4604 := h106293;
    (Or.elim h95339 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step123766 (p2598 p2946 p3146 p3156 p3422 p3564 p4604 p4786 : Prop)
    (h106293 : p4604)
    (h106425 : p4786)
    (h95340 : (¬ p2946) ∨ p3422 ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2598 ∨ (¬ p4604) ∨ p3564 ∨ (¬ p4786))
    : p3422 ∨ (¬ p2946) ∨ p2598 ∨ (¬ p3156) ∨ (¬ p3146) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4604 := h106293;
    let u7 : p4786 := h106425;
    (Or.elim h95340 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123773 (p2427 p3051 p3346 p4399 p4949 : Prop)
    (h105463 : p4949)
    (h95369 : (¬ p3051) ∨ p2427 ∨ (¬ p4949) ∨ (¬ p3346) ∨ (¬ p4399))
    : (¬ p3051) ∨ (¬ p3346) ∨ (¬ p4399) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4949 := h105463;
    (Or.elim h95369 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123774 (p2156 p2470 p2563 p4399 p4608 : Prop)
    (h105540 : p4608)
    (h95370 : (¬ p4399) ∨ p2470 ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4608))
    : p2470 ∨ (¬ p2156) ∨ (¬ p4399) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4608 := h105540;
    (Or.elim h95370 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123779 (p2241 p2459 p2641 p2911 p3323 p3389 p4604 p5190 : Prop)
    (h106293 : p4604)
    (h105487 : p5190)
    (h95379 : p2641 ∨ (¬ p5190) ∨ p3323 ∨ (¬ p4604) ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3389) ∨ p2241)
    : p2241 ∨ p2641 ∨ (¬ p3389) ∨ (¬ p2911) ∨ p3323 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4604 := h106293;
    let u7 : p5190 := h105487;
    (Or.elim h95379 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step123780 (p2230 p2241 p2563 p3125 p3189 p3256 p4330 p5190 : Prop)
    (h105487 : p5190)
    (h106329 : p4330)
    (h95384 : p3256 ∨ p2241 ∨ (¬ p2563) ∨ (¬ p4330) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p3125) ∨ p3189)
    : (¬ p2230) ∨ p3189 ∨ p2241 ∨ (¬ p3125) ∨ (¬ p2563) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5190 := h105487;
    let u7 : p4330 := h106329;
    (Or.elim h95384 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step123781 (p2177 p2553 p2573 p3073 p3256 p3449 p4041 p5190 : Prop)
    (h105487 : p5190)
    (h95387 : p3073 ∨ p3449 ∨ (¬ p5190) ∨ (¬ p4041) ∨ (¬ p2553) ∨ (¬ p3256) ∨ (¬ p2177) ∨ (¬ p2573))
    : (¬ p3256) ∨ (¬ p2573) ∨ (¬ p4041) ∨ p3073 ∨ (¬ p2553) ∨ p3449 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h95387 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step123787 (p2383 p2598 p2742 p2778 p3063 p4752 p4759 : Prop)
    (h105434 : p4752)
    (h95436 : (¬ p3063) ∨ (¬ p2742) ∨ (¬ p2778) ∨ p2383 ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p4759))
    : (¬ p2778) ∨ (¬ p2742) ∨ p2383 ∨ (¬ p2598) ∨ (¬ p4759) ∨ (¬ p3063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4752 := h105434;
    (Or.elim h95436 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step123790 (p2383 p2761 p2778 p2819 p3276 p3355 p3917 p4419 p4625 : Prop)
    (h106455 : p4625)
    (h95448 : p2761 ∨ (¬ p2819) ∨ (¬ p4625) ∨ p2383 ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4419) ∨ (¬ p2778) ∨ (¬ p3355))
    : (¬ p3276) ∨ (¬ p2819) ∨ p2383 ∨ (¬ p2778) ∨ (¬ p3917) ∨ p2761 ∨ (¬ p3355) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    (Or.elim h95448 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step123791 (p2122 p2210 p2241 p2307 p2744 p2778 p2972 p3366 p3917 p4397 : Prop)
    (h106503 : p2744)
    (h95449 : (¬ p2778) ∨ (¬ p2122) ∨ p2241 ∨ p2307 ∨ (¬ p2210) ∨ (¬ p4397) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2972) ∨ (¬ p3917))
    : (¬ p3917) ∨ (¬ p2122) ∨ (¬ p2778) ∨ p2241 ∨ p2307 ∨ (¬ p2210) ∨ (¬ p4397) ∨ (¬ p3366) ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h95449 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step123797 (p2573 p3346 p3564 p4330 p4440 : Prop)
    (h106329 : p4330)
    (h64987 : (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4440))
    : (¬ p2573) ∨ (¬ p3564) ∨ (¬ p3346) ∨ (¬ p4440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4330 := h106329;
    (Or.elim h64987 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step123800 (p2651 p2807 p3201 p3579 p4750 : Prop)
    (h105433 : p4750)
    (h95490 : p2651 ∨ p3201 ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4750))
    : p3201 ∨ p2651 ∨ (¬ p2807) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h95490 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123802 (p2396 p2807 p3286 p3579 p4276 p4656 : Prop)
    (h105516 : p4276)
    (h95499 : (¬ p4656) ∨ (¬ p2396) ∨ (¬ p3579) ∨ (¬ p2807) ∨ p3286 ∨ (¬ p4276))
    : p3286 ∨ (¬ p3579) ∨ (¬ p4656) ∨ (¬ p2396) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4276 := h105516;
    (Or.elim h95499 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step123806 (p2553 p3333 p3422 p4331 p4624 : Prop)
    (h105408 : p4624)
    (h95560 : (¬ p4331) ∨ (¬ p3333) ∨ p3422 ∨ p2553 ∨ (¬ p4624))
    : (¬ p4331) ∨ (¬ p3333) ∨ p2553 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    (Or.elim h95560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123810 (p2264 p2459 p2573 p2807 p3333 p3362 p3422 p4332 p4789 : Prop)
    (h105646 : p4789)
    (h95570 : p2459 ∨ p2264 ∨ (¬ p3333) ∨ (¬ p2573) ∨ (¬ p4332) ∨ (¬ p3362) ∨ p2807 ∨ (¬ p4789) ∨ p3422)
    : (¬ p3333) ∨ p3422 ∨ (¬ p2573) ∨ (¬ p3362) ∨ p2807 ∨ p2264 ∨ p2459 ∨ (¬ p4332) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    (Or.elim h95570 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step123813 (p2573 p2946 p3146 p3156 p3333 p3362 p3422 p4330 p4331 p4789 : Prop)
    (h106329 : p4330)
    (h105646 : p4789)
    (h95577 : (¬ p4331) ∨ p3422 ∨ (¬ p4789) ∨ p3156 ∨ (¬ p3362) ∨ p3146 ∨ (¬ p4330) ∨ (¬ p3333) ∨ p2946 ∨ (¬ p2573))
    : (¬ p3333) ∨ p3422 ∨ (¬ p2573) ∨ p2946 ∨ p3146 ∨ p3156 ∨ (¬ p3362) ∨ (¬ p4331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    let u9 : p4789 := h105646;
    (Or.elim h95577 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step123814 (p2696 p2753 p2761 p3333 p3367 p3645 p4032 p4243 p4322 p4638 p5052 : Prop)
    (h105473 : p5052)
    (h105409 : p4638)
    (h95579 : (¬ p3333) ∨ p2753 ∨ (¬ p5052) ∨ p2696 ∨ (¬ p3367) ∨ (¬ p2761) ∨ (¬ p4322) ∨ (¬ p4638) ∨ (¬ p4032) ∨ (¬ p3645) ∨ (¬ p4243))
    : (¬ p4032) ∨ (¬ p4322) ∨ (¬ p3333) ∨ p2753 ∨ (¬ p3367) ∨ (¬ p2761) ∨ p2696 ∨ (¬ p3645) ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2753) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5052 := h105473;
    let u10 : p4638 := h105409;
    (Or.elim h95579 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step123821 (p2252 p2264 p2598 p2750 p2753 p2807 p3276 p3333 p5123 p5558 : Prop)
    (h106345 : p2750)
    (h95600 : (¬ p3333) ∨ (¬ p5558) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p5123) ∨ p2264 ∨ (¬ p2252) ∨ p2807 ∨ (¬ p3276))
    : (¬ p3276) ∨ (¬ p3333) ∨ p2264 ∨ (¬ p2598) ∨ p2807 ∨ (¬ p5558) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    (Or.elim h95600 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step123823 (p2651 p3136 p3146 p3276 p3333 p3661 p3969 p4343 p4790 p5600 : Prop)
    (h106424 : p4790)
    (h95606 : (¬ p3969) ∨ (¬ p5600) ∨ (¬ p4343) ∨ (¬ p3333) ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p3661) ∨ p3146 ∨ (¬ p4790) ∨ p3136)
    : (¬ p3276) ∨ (¬ p4343) ∨ (¬ p2651) ∨ (¬ p3333) ∨ p3146 ∨ (¬ p5600) ∨ p3136 ∨ (¬ p3969) ∨ (¬ p3661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4790 := h106424;
    (Or.elim h95606 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u6 r8)))))))))))))))))))))

theorem step123825 (p2230 p2331 p2363 p2668 p2850 p3333 p3362 p4332 p4789 : Prop)
    (h105646 : p4789)
    (h95609 : (¬ p3333) ∨ p2363 ∨ (¬ p4332) ∨ (¬ p4789) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p3362) ∨ p2331 ∨ p2850)
    : (¬ p3362) ∨ (¬ p2230) ∨ (¬ p3333) ∨ (¬ p4332) ∨ p2668 ∨ p2331 ∨ p2363 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    (Or.elim h95609 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (u7 r7)))))))))))))))))))

theorem step123826 (p2331 p2363 p2668 p3201 p3333 p3362 p3389 p4332 p4789 : Prop)
    (h105646 : p4789)
    (h95610 : (¬ p3333) ∨ p2363 ∨ (¬ p3362) ∨ (¬ p4332) ∨ (¬ p3389) ∨ p2331 ∨ (¬ p4789) ∨ p3201 ∨ p2668)
    : (¬ p3333) ∨ p3201 ∨ (¬ p3389) ∨ (¬ p4332) ∨ p2668 ∨ p2331 ∨ (¬ p3362) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    (Or.elim h95610 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step123830 (p2252 p2331 p2598 p2668 p2750 p2753 p3276 p3333 p5123 p5580 : Prop)
    (h106345 : p2750)
    (h95625 : (¬ p5580) ∨ (¬ p2753) ∨ p2331 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p2598) ∨ (¬ p2750) ∨ p2668 ∨ (¬ p5123) ∨ (¬ p2252))
    : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p2598) ∨ p2331 ∨ (¬ p2753) ∨ p2668 ∨ (¬ p5580) ∨ (¬ p2252) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    (Or.elim h95625 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step123831 (p2230 p2264 p2459 p2807 p2850 p3333 p3362 p4332 p4789 : Prop)
    (h105646 : p4789)
    (h95627 : (¬ p3333) ∨ (¬ p4332) ∨ (¬ p4789) ∨ (¬ p3362) ∨ p2850 ∨ p2807 ∨ p2264 ∨ p2459 ∨ (¬ p2230))
    : p2850 ∨ (¬ p4332) ∨ p2459 ∨ p2264 ∨ (¬ p2230) ∨ (¬ p3333) ∨ (¬ p3362) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    (Or.elim h95627 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step123835 (p2177 p2295 p2331 p3333 p3346 p3641 p3905 p4438 p4786 : Prop)
    (h106425 : p4786)
    (h95643 : (¬ p3333) ∨ (¬ p3346) ∨ (¬ p2295) ∨ (¬ p4786) ∨ (¬ p4438) ∨ (¬ p3905) ∨ (¬ p2331) ∨ p3641 ∨ (¬ p2177))
    : (¬ p3333) ∨ p3641 ∨ (¬ p3905) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p4438) ∨ (¬ p3346) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    (Or.elim h95643 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step123837 (p2139 p2156 p2264 p2427 p2563 p2717 p3425 p4362 : Prop)
    (h106173 : p4362)
    (h95650 : p2717 ∨ (¬ p2427) ∨ (¬ p2264) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3425) ∨ (¬ p4362) ∨ p2563)
    : p2717 ∨ (¬ p3425) ∨ (¬ p2264) ∨ (¬ p2156) ∨ p2563 ∨ (¬ p2427) ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4362 := h106173;
    (Or.elim h95650 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step123841 (p2156 p2341 p2881 p4555 p4984 : Prop)
    (h105542 : p4555)
    (h95678 : p2341 ∨ (¬ p2881) ∨ (¬ p2156) ∨ (¬ p4984) ∨ (¬ p4555))
    : (¬ p4984) ∨ (¬ p2156) ∨ p2341 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4984 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h95678 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123842 (p2341 p2427 p2881 p4533 p4984 : Prop)
    (h105394 : p4533)
    (h95679 : p2341 ∨ (¬ p2881) ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p4533))
    : p2341 ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h95679 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123844 (p2220 p2437 p3016 p3096 p3575 p4509 p4984 : Prop)
    (h105392 : p4509)
    (h95683 : (¬ p2437) ∨ p3016 ∨ (¬ p3096) ∨ (¬ p4509) ∨ (¬ p4984) ∨ (¬ p3575) ∨ (¬ p2220))
    : (¬ p3575) ∨ (¬ p4984) ∨ (¬ p2437) ∨ (¬ p2220) ∨ p3016 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3575 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4509 := h105392;
    (Or.elim h95683 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step123845 (p2427 p3246 p3516 p4533 p4984 : Prop)
    (h105394 : p4533)
    (h95685 : (¬ p3246) ∨ p3516 ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p4533))
    : (¬ p3246) ∨ (¬ p2427) ∨ (¬ p4984) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h95685 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123846 (p2140 p2870 p3246 p3516 p4984 : Prop)
    (h105364 : p2140)
    (h95686 : (¬ p3246) ∨ p3516 ∨ (¬ p2140) ∨ (¬ p2870) ∨ (¬ p4984))
    : (¬ p2870) ∨ p3516 ∨ (¬ p4984) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h95686 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123847 (p2341 p2563 p2881 p3872 p4533 p4984 : Prop)
    (h105394 : p4533)
    (h95688 : p2341 ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p4533) ∨ (¬ p2563) ∨ (¬ p4984))
    : p2341 ∨ (¬ p4984) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4533 := h105394;
    (Or.elim h95688 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step123853 (p2156 p2166 p2220 p2284 p4960 : Prop)
    (h106209 : p4960)
    (h95772 : p2220 ∨ p2284 ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4960))
    : p2220 ∨ (¬ p2156) ∨ p2284 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h95772 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123854 (p2210 p2284 p3093 p4516 p4960 : Prop)
    (h106209 : p4960)
    (h95773 : (¬ p3093) ∨ p2210 ∨ (¬ p4960) ∨ p2284 ∨ (¬ p4516))
    : p2210 ∨ (¬ p4516) ∨ p2284 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h95773 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step123856 (p2608 p2829 p3379 p3590 p5224 : Prop)
    (h105494 : p5224)
    (h95796 : p3379 ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3590) ∨ (¬ p5224))
    : p3379 ∨ (¬ p2829) ∨ (¬ p2608) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5224 := h105494;
    (Or.elim h95796 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123861 (p2249 p2449 p2996 p3516 p4849 : Prop)
    (h106513 : p2249)
    (h95818 : p3516 ∨ p2996 ∨ (¬ p4849) ∨ (¬ p2449) ∨ (¬ p2249))
    : (¬ p2449) ∨ p2996 ∨ (¬ p4849) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2249 := h106513;
    (Or.elim h95818 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123862 (p2156 p2249 p2459 p2807 p2951 p2992 p3037 p3125 p3527 p4330 : Prop)
    (h106513 : p2249)
    (h106329 : p4330)
    (h95859 : (¬ p3125) ∨ (¬ p2992) ∨ (¬ p3037) ∨ p2807 ∨ p3527 ∨ (¬ p4330) ∨ p2459 ∨ (¬ p2951) ∨ (¬ p2249) ∨ (¬ p2156))
    : (¬ p2156) ∨ p3527 ∨ (¬ p3037) ∨ (¬ p3125) ∨ p2459 ∨ (¬ p2951) ∨ p2807 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4330 := h106329;
    (Or.elim h95859 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step123870 (p2295 p2307 p2651 p3987 p4975 : Prop)
    (h105464 : p4975)
    (h95896 : (¬ p3987) ∨ (¬ p2307) ∨ (¬ p4975) ∨ p2295 ∨ p2651)
    : p2651 ∨ (¬ p2307) ∨ (¬ p3987) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h95896 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step123871 (p2230 p2331 p2440 p2655 p4975 : Prop)
    (h105464 : p4975)
    (h95897 : (¬ p2331) ∨ p2440 ∨ (¬ p2655) ∨ (¬ p4975) ∨ p2230)
    : (¬ p2655) ∨ p2230 ∨ (¬ p2331) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h95897 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step123873 (p2396 p2437 p3083 p3543 p4279 p4404 p4427 p4666 : Prop)
    (h105658 : p4666)
    (h95904 : (¬ p4279) ∨ (¬ p3083) ∨ p2396 ∨ p2437 ∨ (¬ p3543) ∨ (¬ p4666) ∨ (¬ p4427) ∨ (¬ p4404))
    : (¬ p4279) ∨ (¬ p3543) ∨ (¬ p4404) ∨ (¬ p4427) ∨ p2396 ∨ (¬ p3083) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4279 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h95904 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step123874 (p2449 p2922 p3516 p3580 p4279 p4811 : Prop)
    (h105633 : p4811)
    (h95914 : p3516 ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4279) ∨ (¬ p4811) ∨ p2922)
    : p2922 ∨ (¬ p2449) ∨ p3516 ∨ (¬ p3580) ∨ (¬ p4279) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h95914 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step123878 (p2341 p2881 p2901 p2954 p4984 : Prop)
    (h106494 : p2954)
    (h95944 : (¬ p2954) ∨ (¬ p4984) ∨ p2341 ∨ (¬ p2901) ∨ (¬ p2881))
    : (¬ p4984) ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4984 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h95944 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step123879 (p2187 p2284 p2383 p2954 p4198 : Prop)
    (h106494 : p2954)
    (h95947 : (¬ p2187) ∨ p2383 ∨ (¬ p4198) ∨ (¬ p2954) ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p4198) ∨ (¬ p2187) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h95947 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step123884 (p2143 p2427 p2696 p2829 p2982 p3051 p3366 p3483 p4368 p5052 : Prop)
    (h105473 : p5052)
    (h95958 : p3051 ∨ (¬ p2427) ∨ (¬ p2829) ∨ (¬ p3483) ∨ p2982 ∨ (¬ p3366) ∨ (¬ p2143) ∨ (¬ p5052) ∨ p2696 ∨ (¬ p4368))
    : (¬ p2829) ∨ p3051 ∨ (¬ p3483) ∨ p2982 ∨ (¬ p2427) ∨ p2696 ∨ (¬ p3366) ∨ (¬ p2143) ∨ (¬ p4368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5052 := h105473;
    (Or.elim h95958 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step123885 (p4136 p4782 p5052 : Prop)
    (h105473 : p5052)
    (h36450 : (¬ p4136) ∨ p4782 ∨ (¬ p5052))
    : (¬ p4136) ∨ p4782 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4782) := (fun h => hn (Or.inr h));
    let u2 : p5052 := h105473;
    (Or.elim h36450 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step123886 (p2341 p2437 p3083 p4383 p5203 : Prop)
    (h105490 : p5203)
    (h95959 : p3083 ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4383) ∨ (¬ p5203))
    : (¬ p2341) ∨ p3083 ∨ (¬ p4383) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5203 := h105490;
    (Or.elim h95959 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123887 (p2307 p2505 p2850 p3309 p4031 p4198 p5217 : Prop)
    (h105493 : p5217)
    (h95961 : (¬ p3309) ∨ p2307 ∨ (¬ p4031) ∨ (¬ p5217) ∨ (¬ p2505) ∨ (¬ p4198) ∨ p2850)
    : (¬ p4198) ∨ p2850 ∨ (¬ p2505) ∨ (¬ p3309) ∨ p2307 ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5217 := h105493;
    (Or.elim h95961 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (u1 r5)))))))))))))))

theorem step123888 (p2553 p2573 p3166 p3256 p3266 p3791 p4236 p4419 p4826 : Prop)
    (h105444 : p4826)
    (h95975 : p3166 ∨ p3256 ∨ (¬ p4826) ∨ p3266 ∨ (¬ p2573) ∨ (¬ p4236) ∨ (¬ p3791) ∨ (¬ p4419) ∨ (¬ p2553))
    : (¬ p3791) ∨ p3166 ∨ p3266 ∨ (¬ p2573) ∨ p3256 ∨ (¬ p4236) ∨ (¬ p2553) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4826 := h105444;
    (Or.elim h95975 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step123890 (p2187 p2241 p2274 p2307 p2727 p3083 p4384 p5017 : Prop)
    (h106167 : p4384)
    (h95989 : (¬ p5017) ∨ (¬ p2187) ∨ p3083 ∨ (¬ p2307) ∨ p2274 ∨ p2241 ∨ p2727 ∨ (¬ p4384))
    : (¬ p2307) ∨ p2241 ∨ p2274 ∨ (¬ p5017) ∨ (¬ p2187) ∨ p3083 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4384 := h106167;
    (Or.elim h95989 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123891 (p2177 p2210 p2319 p2341 p2396 p2608 p2972 p3951 p4866 p5016 : Prop)
    (h106063 : p4866)
    (h106536 : p3951)
    (h96019 : (¬ p2608) ∨ (¬ p2319) ∨ (¬ p2396) ∨ (¬ p2341) ∨ (¬ p4866) ∨ p2972 ∨ p2210 ∨ p2177 ∨ (¬ p5016) ∨ (¬ p3951))
    : p2972 ∨ (¬ p5016) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ p2210 ∨ (¬ p2608) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4866 := h106063;
    let u9 : p3951 := h106536;
    (Or.elim h96019 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step123893 (p2396 p2437 p3343 p4276 p4636 : Prop)
    (h105516 : p4276)
    (h96034 : p3343 ∨ (¬ p4636) ∨ (¬ p2437) ∨ (¬ p2396) ∨ (¬ p4276))
    : (¬ p4636) ∨ p3343 ∨ (¬ p2396) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4636 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h96034 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step123900 (p2982 p3680 p3707 p4282 p4702 p4938 : Prop)
    (h106079 : p4702)
    (h96057 : p3707 ∨ (¬ p4282) ∨ (¬ p4702) ∨ (¬ p3680) ∨ (¬ p2982) ∨ (¬ p4938))
    : (¬ p3680) ∨ (¬ p2982) ∨ p3707 ∨ (¬ p4938) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    (Or.elim h96057 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step123901 (p2341 p2608 p3527 p3545 p4796 : Prop)
    (h105439 : p4796)
    (h96058 : p3527 ∨ p2608 ∨ (¬ p3545) ∨ (¬ p4796) ∨ (¬ p2341))
    : p2608 ∨ (¬ p2341) ∨ (¬ p3545) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4796 := h105439;
    (Or.elim h96058 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step123904 (p2363 p2383 p2696 p3136 p3266 p3366 p4866 p5016 p5405 p5740 : Prop)
    (h106063 : p4866)
    (h96085 : (¬ p5016) ∨ (¬ p3266) ∨ (¬ p2383) ∨ (¬ p5405) ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p5740) ∨ (¬ p4866) ∨ p3136 ∨ p2696)
    : (¬ p5740) ∨ p3136 ∨ (¬ p2363) ∨ (¬ p5016) ∨ (¬ p2383) ∨ (¬ p3366) ∨ (¬ p3266) ∨ (¬ p5405) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5740 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4866 := h106063;
    (Or.elim h96085 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u8 r8)))))))))))))))))))))

theorem step123914 (p3550 p4998 p5309 : Prop)
    (h105497 : p5309)
    (h23396 : (¬ p3550) ∨ p4998 ∨ (¬ p5309))
    : (¬ p3550) ∨ p4998 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3550 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4998) := (fun h => hn (Or.inr h));
    let u2 : p5309 := h105497;
    (Or.elim h23396 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step123915 (p2341 p2696 p2797 p2881 p3246 p3323 p4625 p5257 : Prop)
    (h106455 : p4625)
    (h96606 : (¬ p2341) ∨ p2797 ∨ p2696 ∨ (¬ p3246) ∨ (¬ p5257) ∨ p3323 ∨ (¬ p4625) ∨ p2881)
    : (¬ p3246) ∨ p2881 ∨ p2696 ∨ p3323 ∨ (¬ p2341) ∨ p2797 ∨ (¬ p5257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4625 := h106455;
    (Or.elim h96606 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step123918 (p2598 p3367 p3399 p3589 p4793 : Prop)
    (h105438 : p4793)
    (h96673 : (¬ p4793) ∨ p3399 ∨ (¬ p3589) ∨ (¬ p2598) ∨ p3367)
    : (¬ p2598) ∨ p3367 ∨ p3399 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4793 := h105438;
    (Or.elim h96673 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step123920 (p2253 p2651 p2727 p2741 p3399 p4793 : Prop)
    (h105438 : p4793)
    (h96675 : p2727 ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p4793) ∨ (¬ p2741) ∨ p3399)
    : p3399 ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p2741) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4793 := h105438;
    (Or.elim h96675 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step123921 (p2156 p2274 p2396 p2630 p2696 p2753 p3343 p3645 p4638 p4877 : Prop)
    (h105451 : p4877)
    (h105409 : p4638)
    (h96680 : (¬ p4638) ∨ (¬ p3343) ∨ (¬ p2630) ∨ (¬ p2696) ∨ p2396 ∨ (¬ p4877) ∨ (¬ p2753) ∨ p2156 ∨ p2274 ∨ (¬ p3645))
    : (¬ p2696) ∨ p2156 ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3645) ∨ p2274 ∨ p2396 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4877 := h105451;
    let u9 : p4638 := h105409;
    (Or.elim h96680 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step123922 (p2122 p2396 p2470 p2663 p2774 p3083 p3343 p4638 p4786 : Prop)
    (h106425 : p4786)
    (h105409 : p4638)
    (h96681 : (¬ p2470) ∨ (¬ p3343) ∨ p3083 ∨ (¬ p2663) ∨ p2774 ∨ p2122 ∨ (¬ p4638) ∨ (¬ p4786) ∨ p2396)
    : (¬ p2470) ∨ p3083 ∨ (¬ p2663) ∨ p2396 ∨ p2774 ∨ p2122 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : p4638 := h105409;
    (Or.elim h96681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step123924 (p3201 p3914 p4210 p4375 p4435 p4512 p4644 : Prop)
    (h105411 : p4644)
    (h96708 : (¬ p4435) ∨ (¬ p3914) ∨ (¬ p4375) ∨ (¬ p4644) ∨ (¬ p4210) ∨ (¬ p4512) ∨ p3201)
    : (¬ p3914) ∨ p3201 ∨ (¬ p4512) ∨ (¬ p4375) ∨ (¬ p4435) ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4644 := h105411;
    (Or.elim h96708 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (u1 r5)))))))))))))))

theorem step123938 (p2177 p2373 p2406 p2717 p3379 p3425 p4119 p4556 p4736 : Prop)
    (h105431 : p4736)
    (h105399 : p4556)
    (h97027 : p2717 ∨ (¬ p3425) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p4736) ∨ (¬ p2177) ∨ (¬ p3379))
    : p2717 ∨ (¬ p2373) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p3425) ∨ (¬ p2177) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4556 := h105399;
    (Or.elim h97027 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step123939 (p2192 p2210 p2459 p2717 p3125 p3425 p4330 p4736 : Prop)
    (h105431 : p4736)
    (h106329 : p4330)
    (h97028 : p2717 ∨ (¬ p3125) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p4330) ∨ p2459)
    : p2717 ∨ (¬ p3425) ∨ (¬ p3125) ∨ p2459 ∨ (¬ p2210) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4330 := h106329;
    (Or.elim h97028 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step123940 (p2156 p2192 p2717 p2891 p2911 p3425 p4172 p4647 p4736 : Prop)
    (h105431 : p4736)
    (h105412 : p4647)
    (h97030 : (¬ p2891) ∨ p2192 ∨ (¬ p2911) ∨ (¬ p4647) ∨ (¬ p2156) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p4736) ∨ (¬ p4172))
    : (¬ p2891) ∨ p2192 ∨ p2717 ∨ (¬ p3425) ∨ (¬ p2156) ∨ (¬ p2911) ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4647 := h105412;
    (Or.elim h97030 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step123942 (p2459 p2518 p2717 p3379 p3425 p4149 p4736 p5122 : Prop)
    (h105431 : p4736)
    (h105483 : p5122)
    (h97036 : (¬ p4149) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p3379) ∨ (¬ p2518) ∨ (¬ p5122) ∨ p2459 ∨ (¬ p4736))
    : (¬ p4149) ∨ (¬ p2518) ∨ (¬ p3379) ∨ p2459 ∨ (¬ p3425) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p5122 := h105483;
    (Or.elim h97036 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123946 (p2331 p2717 p3323 p3425 p3461 p4786 p5123 p5558 : Prop)
    (h106425 : p4786)
    (h97050 : (¬ p5558) ∨ (¬ p5123) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p4786))
    : p2717 ∨ (¬ p2331) ∨ (¬ p5558) ∨ (¬ p3461) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h97050 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123947 (p2230 p2437 p2440 p2717 p3399 p3527 p5083 p5193 : Prop)
    (h105488 : p5193)
    (h97051 : (¬ p3527) ∨ p2717 ∨ p2440 ∨ (¬ p5193) ∨ p2437 ∨ p2230 ∨ (¬ p5083) ∨ (¬ p3399))
    : p2230 ∨ (¬ p5083) ∨ (¬ p3399) ∨ p2717 ∨ p2440 ∨ (¬ p3527) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h97051 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step123950 (p2717 p3366 p3379 p3425 p3707 p3830 p4042 p4376 p5123 p5568 : Prop)
    (h106320 : p4376)
    (h97061 : (¬ p5568) ∨ p2717 ∨ (¬ p4042) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3830) ∨ (¬ p5123) ∨ (¬ p4376) ∨ (¬ p3707) ∨ p3379)
    : (¬ p3707) ∨ p2717 ∨ (¬ p4042) ∨ (¬ p3425) ∨ (¬ p5123) ∨ (¬ p3366) ∨ (¬ p3830) ∨ (¬ p5568) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h97061 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (u8 r8)))))))))))))))))))))

theorem step123953 (p2177 p2241 p2437 p2717 p2727 p3425 p4276 p4736 : Prop)
    (h105431 : p4736)
    (h105516 : p4276)
    (h97072 : (¬ p3425) ∨ (¬ p2437) ∨ (¬ p2727) ∨ p2717 ∨ (¬ p2241) ∨ (¬ p2177) ∨ (¬ p4276) ∨ (¬ p4736))
    : (¬ p3425) ∨ (¬ p2727) ∨ (¬ p2437) ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4276 := h105516;
    (Or.elim h97072 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123955 (p2230 p2717 p2982 p3366 p3425 p3519 p3680 p4376 p5123 p5558 : Prop)
    (h106320 : p4376)
    (h97077 : (¬ p5558) ∨ (¬ p3680) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2982) ∨ p2717 ∨ (¬ p5123) ∨ (¬ p3425) ∨ (¬ p2230))
    : (¬ p3680) ∨ p2717 ∨ (¬ p5123) ∨ (¬ p2982) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p5558) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h97077 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step123958 (p2192 p2717 p3527 p4344 p4431 p4558 : Prop)
    (h105400 : p4558)
    (h97094 : (¬ p3527) ∨ p2717 ∨ (¬ p4558) ∨ (¬ p4344) ∨ (¬ p4431) ∨ p2192)
    : (¬ p4431) ∨ p2717 ∨ (¬ p3527) ∨ (¬ p4344) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4431 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h97094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step123960 (p2098 p2352 p2459 p2493 p3379 p3609 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h97103 : p3609 ∨ (¬ p2493) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2352) ∨ p2098)
    : (¬ p2493) ∨ p2098 ∨ (¬ p3379) ∨ (¬ p2459) ∨ (¬ p2352) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4133 := h105712;
    (Or.elim h97103 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step123962 (p2098 p2210 p2363 p2881 p2891 p3609 p4503 p4736 : Prop)
    (h105431 : p4736)
    (h106530 : p4503)
    (h97109 : (¬ p2891) ∨ p3609 ∨ (¬ p4736) ∨ (¬ p2881) ∨ p2098 ∨ (¬ p2363) ∨ (¬ p2210) ∨ (¬ p4503))
    : p3609 ∨ p2098 ∨ (¬ p2891) ∨ (¬ p2881) ∨ (¬ p2210) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4503 := h106530;
    (Or.elim h97109 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123965 (p2098 p2241 p2264 p2363 p2996 p3609 p4503 p4736 : Prop)
    (h105431 : p4736)
    (h106530 : p4503)
    (h97120 : p2098 ∨ p2996 ∨ (¬ p2363) ∨ p3609 ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p4503))
    : p3609 ∨ p2098 ∨ (¬ p2264) ∨ (¬ p2241) ∨ p2996 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4503 := h106530;
    (Or.elim h97120 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123968 (p2459 p2641 p2668 p2696 p2742 p3537 p3609 p4133 : Prop)
    (h105712 : p4133)
    (h97129 : p3609 ∨ (¬ p2742) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2696) ∨ (¬ p2668) ∨ p3537 ∨ (¬ p2641))
    : p3537 ∨ (¬ p2459) ∨ (¬ p2668) ∨ (¬ p2696) ∨ p3609 ∨ (¬ p2742) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    (Or.elim h97129 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123969 (p2098 p2352 p2459 p2651 p3016 p3609 p4133 p4786 : Prop)
    (h105712 : p4133)
    (h106425 : p4786)
    (h97131 : p3609 ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p4133) ∨ (¬ p4786) ∨ (¬ p2459) ∨ p2098 ∨ (¬ p3016))
    : p3609 ∨ p2098 ∨ (¬ p2459) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4133 := h105712;
    let u7 : p4786 := h106425;
    (Or.elim h97131 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step123973 (p2098 p2230 p2459 p2563 p3125 p3322 p3609 p4133 p4419 : Prop)
    (h105712 : p4133)
    (h97139 : p3609 ∨ p2098 ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p4419) ∨ (¬ p2230) ∨ (¬ p3125) ∨ (¬ p4133) ∨ (¬ p3322))
    : (¬ p2230) ∨ p3609 ∨ (¬ p3322) ∨ p2098 ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    (Or.elim h97139 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step123976 (p2098 p2230 p2427 p2881 p3256 p3366 p3519 p3609 p4041 p4376 : Prop)
    (h106320 : p4376)
    (h97144 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3256) ∨ p2098 ∨ (¬ p2230) ∨ p3609 ∨ (¬ p3519) ∨ (¬ p4041))
    : p2098 ∨ p3609 ∨ (¬ p3366) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h97144 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step123977 (p2098 p2230 p2363 p2427 p2881 p3366 p3519 p3609 p4376 p4503 : Prop)
    (h106530 : p4503)
    (h106320 : p4376)
    (h97145 : (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4376) ∨ p3609 ∨ (¬ p3519) ∨ (¬ p4503) ∨ (¬ p2881) ∨ (¬ p2363) ∨ p2098 ∨ (¬ p3366))
    : p2098 ∨ (¬ p2230) ∨ p3609 ∨ (¬ p2363) ∨ (¬ p2427) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : p4376 := h106320;
    (Or.elim h97145 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step123979 (p2098 p2363 p2911 p2922 p3379 p3609 p4503 p4736 : Prop)
    (h105431 : p4736)
    (h106530 : p4503)
    (h97147 : p3609 ∨ (¬ p4503) ∨ (¬ p3379) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p4736) ∨ p2098 ∨ (¬ p2922))
    : p3609 ∨ p2098 ∨ (¬ p3379) ∨ (¬ p2911) ∨ (¬ p2363) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4503 := h106530;
    (Or.elim h97147 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step123980 (p2248 p2608 p2651 p3016 p3537 p3564 p3609 p4330 : Prop)
    (h105365 : p2248)
    (h106329 : p4330)
    (h97151 : p3609 ∨ (¬ p3564) ∨ (¬ p4330) ∨ p2608 ∨ (¬ p2651) ∨ (¬ p3016) ∨ p3537 ∨ (¬ p2248))
    : p3537 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3016) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4330 := h106329;
    (Or.elim h97151 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123981 (p2098 p2363 p3366 p3379 p3399 p3527 p3609 p4376 p4503 : Prop)
    (h106530 : p4503)
    (h106320 : p4376)
    (h97166 : (¬ p3399) ∨ (¬ p3366) ∨ (¬ p2363) ∨ p3379 ∨ p3609 ∨ p2098 ∨ (¬ p4503) ∨ (¬ p3527) ∨ (¬ p4376))
    : (¬ p3527) ∨ (¬ p3399) ∨ p3609 ∨ p3379 ∨ (¬ p2363) ∨ p2098 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4503 := h106530;
    let u8 : p4376 := h106320;
    (Or.elim h97166 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step123984 (p2098 p2248 p2363 p2881 p2901 p2946 p3609 p3873 p4503 : Prop)
    (h105365 : p2248)
    (h106530 : p4503)
    (h97179 : p3609 ∨ (¬ p2901) ∨ (¬ p2881) ∨ p2098 ∨ (¬ p4503) ∨ (¬ p2363) ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p3873))
    : p2098 ∨ p3609 ∨ (¬ p2363) ∨ (¬ p2901) ∨ (¬ p3873) ∨ (¬ p2946) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4503 := h106530;
    (Or.elim h97179 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step123985 (p2248 p2608 p2901 p2946 p3246 p3537 p3609 p3950 : Prop)
    (h105365 : p2248)
    (h97180 : (¬ p3246) ∨ (¬ p2946) ∨ (¬ p3950) ∨ (¬ p2248) ∨ p2608 ∨ p3609 ∨ p3537 ∨ (¬ p2901))
    : (¬ p2901) ∨ p3537 ∨ p3609 ∨ (¬ p3246) ∨ (¬ p2946) ∨ p2608 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h97180 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step123987 (p2098 p2187 p2230 p2563 p3256 p3609 p3873 p4774 p5190 : Prop)
    (h105487 : p5190)
    (h97192 : (¬ p3256) ∨ p3609 ∨ (¬ p4774) ∨ (¬ p2230) ∨ p2098 ∨ (¬ p3873) ∨ (¬ p5190) ∨ (¬ p2187) ∨ (¬ p2563))
    : p2098 ∨ p3609 ∨ (¬ p4774) ∨ (¬ p2187) ∨ (¬ p3873) ∨ (¬ p2563) ∨ (¬ p3256) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5190 := h105487;
    (Or.elim h97192 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step123988 (p2230 p2427 p2608 p3246 p3537 p3609 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h97194 : (¬ p2427) ∨ (¬ p2230) ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p5190) ∨ p2608 ∨ p3537 ∨ p3609)
    : (¬ p3246) ∨ (¬ p2427) ∨ p3609 ∨ p3537 ∨ (¬ p3950) ∨ (¬ p2230) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h97194 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step123989 (p2248 p2417 p2437 p2608 p2651 p3537 p3609 p3950 : Prop)
    (h105365 : p2248)
    (h97197 : p3537 ∨ p3609 ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2437) ∨ p2608 ∨ (¬ p2248) ∨ (¬ p3950))
    : p2608 ∨ (¬ p2417) ∨ (¬ p2437) ∨ p3537 ∨ (¬ p2651) ∨ p3609 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h97197 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step123990 (p2098 p2437 p2651 p3266 p3609 p3868 p4786 p4826 : Prop)
    (h106425 : p4786)
    (h105444 : p4826)
    (h97199 : (¬ p3868) ∨ p2098 ∨ p3266 ∨ p3609 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p4786) ∨ (¬ p4826))
    : (¬ p3868) ∨ p2098 ∨ p3266 ∨ p3609 ∨ (¬ p2437) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4826 := h105444;
    (Or.elim h97199 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step123992 (p2396 p2553 p2573 p2608 p3537 p3609 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h97204 : p2608 ∨ p3609 ∨ (¬ p2553) ∨ (¬ p5190) ∨ (¬ p3950) ∨ (¬ p2573) ∨ (¬ p2396) ∨ p3537)
    : p3537 ∨ p2608 ∨ (¬ p3950) ∨ p3609 ∨ (¬ p2553) ∨ (¬ p2396) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h97204 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step123993 (p2248 p2284 p2608 p2946 p3125 p3537 p3609 p4330 : Prop)
    (h105365 : p2248)
    (h106329 : p4330)
    (h97206 : p3609 ∨ p2608 ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p4330) ∨ (¬ p2284) ∨ p3537)
    : p3609 ∨ p2608 ∨ (¬ p3125) ∨ p3537 ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4330 := h106329;
    (Or.elim h97206 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step123995 (p2248 p2295 p2331 p2396 p2608 p3537 p3609 p3950 : Prop)
    (h105365 : p2248)
    (h97209 : p3609 ∨ (¬ p2248) ∨ (¬ p2396) ∨ (¬ p2295) ∨ (¬ p2331) ∨ p2608 ∨ p3537 ∨ (¬ p3950))
    : p3537 ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p2295) ∨ (¬ p2331) ∨ p3609 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h97209 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124000 (p2437 p2651 p2774 p3461 p3868 p3917 p4786 p4826 : Prop)
    (h106425 : p4786)
    (h105444 : p4826)
    (h97232 : p3461 ∨ (¬ p3868) ∨ (¬ p4786) ∨ (¬ p2437) ∨ (¬ p3917) ∨ (¬ p2651) ∨ (¬ p4826) ∨ p2774)
    : (¬ p3868) ∨ (¬ p3917) ∨ p3461 ∨ p2774 ∨ (¬ p2651) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4826 := h105444;
    (Or.elim h97232 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step124002 (p2254 p2331 p2608 p2707 p3323 p3461 p4253 p4826 : Prop)
    (h105366 : p2254)
    (h105444 : p4826)
    (h97236 : (¬ p4253) ∨ p3461 ∨ (¬ p2254) ∨ p3323 ∨ (¬ p2707) ∨ (¬ p4826) ∨ p2331 ∨ (¬ p2608))
    : (¬ p4253) ∨ (¬ p2707) ∨ p3323 ∨ p3461 ∨ (¬ p2608) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4826 := h105444;
    (Or.elim h97236 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124004 (p2363 p2459 p3256 p3564 p4503 : Prop)
    (h106530 : p4503)
    (h97245 : (¬ p3564) ∨ p3256 ∨ (¬ p4503) ∨ p2459 ∨ (¬ p2363))
    : p3256 ∨ p2459 ∨ (¬ p2363) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    (Or.elim h97245 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124008 (p2241 p2528 p2598 p2641 p3323 p3641 p4330 p4736 : Prop)
    (h105431 : p4736)
    (h106329 : p4330)
    (h97291 : p2528 ∨ p3641 ∨ (¬ p4736) ∨ p2598 ∨ (¬ p4330) ∨ (¬ p3323) ∨ (¬ p2241) ∨ (¬ p2641))
    : p3641 ∨ p2598 ∨ (¬ p3323) ∨ (¬ p2641) ∨ p2528 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4330 := h106329;
    (Or.elim h97291 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124010 (p2246 p2284 p2528 p2598 p2744 p2946 p3125 p3366 p3641 p4330 : Prop)
    (h106503 : p2744)
    (h106329 : p4330)
    (h97297 : (¬ p3125) ∨ p2528 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p3641 ∨ (¬ p2946) ∨ p2598 ∨ (¬ p4330) ∨ (¬ p2284))
    : p3641 ∨ (¬ p2246) ∨ p2598 ∨ (¬ p2284) ∨ (¬ p3125) ∨ p2528 ∨ (¬ p2946) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4330 := h106329;
    (Or.elim h97297 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step124012 (p2210 p2528 p2598 p2891 p3246 p3641 p3950 p4736 : Prop)
    (h105431 : p4736)
    (h97303 : p2528 ∨ (¬ p2210) ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p4736) ∨ (¬ p2891) ∨ p2598 ∨ p3641)
    : (¬ p2891) ∨ p3641 ∨ p2598 ∨ (¬ p3246) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97303 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124015 (p2139 p2573 p2901 p3051 p3156 p3422 p3641 p3905 p4434 : Prop)
    (h106144 : p4434)
    (h97309 : p2901 ∨ (¬ p3156) ∨ (¬ p4434) ∨ (¬ p2139) ∨ (¬ p3051) ∨ (¬ p3422) ∨ p3641 ∨ p2573 ∨ (¬ p3905))
    : p3641 ∨ (¬ p3422) ∨ (¬ p2139) ∨ p2573 ∨ (¬ p3156) ∨ (¬ p3051) ∨ (¬ p3905) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4434 := h106144;
    (Or.elim h97309 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124016 (p2187 p3422 p3641 p3958 p4432 : Prop)
    (h105378 : p3958)
    (h97311 : p3641 ∨ (¬ p3422) ∨ (¬ p2187) ∨ (¬ p3958) ∨ (¬ p4432))
    : p3641 ∨ (¬ p3422) ∨ (¬ p2187) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    (Or.elim h97311 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124017 (p2187 p2573 p3641 p3759 p3958 p4432 : Prop)
    (h105378 : p3958)
    (h97313 : p3641 ∨ (¬ p2573) ∨ (¬ p4432) ∨ (¬ p2187) ∨ (¬ p3958) ∨ (¬ p3759))
    : p3641 ∨ (¬ p3759) ∨ (¬ p2187) ∨ (¬ p4432) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h97313 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step124022 (p2254 p2901 p2911 p2922 p2946 p3246 p3379 p4666 : Prop)
    (h105366 : p2254)
    (h105658 : p4666)
    (h97331 : p3246 ∨ (¬ p2911) ∨ p2946 ∨ (¬ p2922) ∨ (¬ p4666) ∨ p2901 ∨ (¬ p2254) ∨ (¬ p3379))
    : p2946 ∨ p2901 ∨ (¬ p2922) ∨ p3246 ∨ (¬ p3379) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4666 := h105658;
    (Or.elim h97331 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124025 (p2122 p2177 p2753 p2774 p3379 p3399 p4442 p5559 : Prop)
    (h106189 : p5559)
    (h97336 : (¬ p2753) ∨ (¬ p4442) ∨ (¬ p5559) ∨ p3399 ∨ (¬ p2122) ∨ (¬ p3379) ∨ (¬ p2177) ∨ (¬ p2774))
    : (¬ p4442) ∨ (¬ p2774) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2177) ∨ (¬ p2122) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5559 := h106189;
    (Or.elim h97336 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124027 (p2241 p2608 p3367 p4752 : Prop)
    (h105434 : p4752)
    (h97347 : p2241 ∨ (¬ p2608) ∨ (¬ p4752) ∨ (¬ p3367))
    : p2241 ∨ (¬ p3367) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4752 := h105434;
    (Or.elim h97347 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step124029 (p2254 p2608 p2707 p2946 p3146 p3156 p3434 p3950 : Prop)
    (h105366 : p2254)
    (h97349 : (¬ p3434) ∨ p3146 ∨ p3156 ∨ (¬ p3950) ∨ (¬ p2608) ∨ p2946 ∨ (¬ p2254) ∨ (¬ p2707))
    : (¬ p3434) ∨ p3156 ∨ p2946 ∨ (¬ p2608) ∨ (¬ p2707) ∨ p3146 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h97349 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124030 (p2122 p2254 p2264 p2608 p2807 p2829 p2881 p4559 : Prop)
    (h105366 : p2254)
    (h105701 : p4559)
    (h97352 : (¬ p2881) ∨ (¬ p2122) ∨ p2807 ∨ (¬ p2608) ∨ p2264 ∨ (¬ p4559) ∨ (¬ p2254) ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p2881) ∨ (¬ p2608) ∨ p2264 ∨ p2807 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4559 := h105701;
    (Or.elim h97352 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124038 (p2352 p2493 p2608 p3707 p3830 p3979 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h97368 : p3707 ∨ p3830 ∨ (¬ p2608) ∨ (¬ p3979) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p4376) ∨ (¬ p5119))
    : (¬ p3979) ∨ (¬ p2608) ∨ (¬ p2493) ∨ (¬ p2352) ∨ p3707 ∨ p3830 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    (Or.elim h97368 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124040 (p2187 p2246 p2284 p2608 p2744 p2946 p3399 p3527 p4133 : Prop)
    (h106503 : p2744)
    (h105712 : p4133)
    (h97371 : p3399 ∨ (¬ p2284) ∨ (¬ p2744) ∨ p3527 ∨ (¬ p2246) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2946) ∨ (¬ p2608))
    : (¬ p2608) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p2284) ∨ p3527 ∨ (¬ p2187) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4133 := h105712;
    (Or.elim h97371 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step124044 (p2246 p2608 p2744 p2946 p3093 p3146 p3156 p3319 p4604 : Prop)
    (h106503 : p2744)
    (h106293 : p4604)
    (h97381 : p3093 ∨ (¬ p2246) ∨ (¬ p4604) ∨ (¬ p2608) ∨ (¬ p2744) ∨ p3319 ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3146))
    : (¬ p2946) ∨ (¬ p3156) ∨ p3319 ∨ (¬ p2246) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4604 := h106293;
    (Or.elim h97381 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124050 (p2230 p2427 p2608 p2881 p3093 p3519 p3923 p4376 p4503 : Prop)
    (h106530 : p4503)
    (h106320 : p4376)
    (h97391 : p3093 ∨ (¬ p3519) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2881) ∨ (¬ p4503) ∨ (¬ p3923) ∨ (¬ p2427) ∨ (¬ p2230))
    : p3093 ∨ (¬ p2608) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3923) ∨ (¬ p2881) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4503 := h106530;
    let u8 : p4376 := h106320;
    (Or.elim h97391 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step124054 (p2187 p2230 p2563 p2608 p2707 p2717 p4503 p5193 : Prop)
    (h106530 : p4503)
    (h105488 : p5193)
    (h97399 : (¬ p2707) ∨ (¬ p2717) ∨ p2187 ∨ p2563 ∨ (¬ p4503) ∨ p2230 ∨ (¬ p5193) ∨ (¬ p2608))
    : (¬ p2717) ∨ p2230 ∨ p2563 ∨ (¬ p2608) ∨ (¬ p2707) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4503 := h106530;
    let u7 : p5193 := h105488;
    (Or.elim h97399 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124056 (p2156 p2192 p2608 p3093 p4377 : Prop)
    (h106170 : p4377)
    (h97400 : p3093 ∨ (¬ p2608) ∨ (¬ p2192) ∨ p2156 ∨ (¬ p4377))
    : p3093 ∨ p2156 ∨ (¬ p2192) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4377 := h106170;
    (Or.elim h97400 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124057 (p2156 p2192 p2608 p3369 p4377 : Prop)
    (h106170 : p4377)
    (h97401 : (¬ p2192) ∨ (¬ p3369) ∨ (¬ p2608) ∨ p2156 ∨ (¬ p4377))
    : (¬ p3369) ∨ p2156 ∨ (¬ p2608) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4377 := h106170;
    (Or.elim h97401 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124058 (p2246 p2295 p2331 p2396 p2608 p2744 p3073 p3449 p3950 : Prop)
    (h106503 : p2744)
    (h97402 : (¬ p2295) ∨ (¬ p2396) ∨ p3449 ∨ (¬ p3950) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ p3073)
    : p3449 ∨ (¬ p2295) ∨ p3073 ∨ (¬ p2246) ∨ (¬ p2396) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h97402 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124061 (p2166 p2220 p2608 p3369 p4377 : Prop)
    (h106170 : p4377)
    (h97405 : (¬ p3369) ∨ p2220 ∨ (¬ p2166) ∨ (¬ p2608) ∨ (¬ p4377))
    : p2220 ∨ (¬ p3369) ∨ (¬ p2166) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4377 := h106170;
    (Or.elim h97405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124063 (p2608 p2891 p3051 p4377 : Prop)
    (h106170 : p4377)
    (h97408 : p3051 ∨ (¬ p2608) ∨ (¬ p2891) ∨ (¬ p4377))
    : p3051 ∨ (¬ p2891) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4377 := h106170;
    (Or.elim h97408 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step124065 (p2187 p2230 p2563 p2608 p2685 p2749 p3755 p3842 p5193 : Prop)
    (h105488 : p5193)
    (h97412 : (¬ p3842) ∨ p3755 ∨ (¬ p2685) ∨ p2563 ∨ (¬ p2749) ∨ (¬ p2608) ∨ (¬ p5193) ∨ p2230 ∨ p2187)
    : p3755 ∨ (¬ p2749) ∨ (¬ p2685) ∨ (¬ p2608) ∨ p2563 ∨ p2187 ∨ (¬ p3842) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5193 := h105488;
    (Or.elim h97412 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (u5 r7)))))))))))))))))))

theorem step124071 (p2166 p2210 p2241 p2573 p2744 p3366 p3422 p3641 p3905 p4434 : Prop)
    (h106503 : p2744)
    (h106144 : p4434)
    (h97435 : p3641 ∨ p2573 ∨ p2241 ∨ (¬ p3905) ∨ (¬ p2210) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2166) ∨ (¬ p3422) ∨ (¬ p4434))
    : p3641 ∨ (¬ p3422) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3366) ∨ p2573 ∨ p2241 ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4434 := h106144;
    (Or.elim h97435 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124072 (p2210 p2254 p2437 p2651 p2891 p2911 p3246 p4668 : Prop)
    (h105366 : p2254)
    (h105414 : p4668)
    (h97436 : (¬ p3246) ∨ p2911 ∨ (¬ p2891) ∨ p2651 ∨ (¬ p4668) ∨ p2437 ∨ (¬ p2210) ∨ (¬ p2254))
    : p2911 ∨ p2437 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4668 := h105414;
    (Or.elim h97436 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124073 (p2122 p2166 p2177 p2210 p2241 p2573 p2744 p3366 p3905 p4390 p4902 : Prop)
    (h106503 : p2744)
    (h105456 : p4902)
    (h97437 : p2573 ∨ p2122 ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3905) ∨ (¬ p2210) ∨ p2177 ∨ (¬ p4902) ∨ (¬ p3366) ∨ (¬ p2166) ∨ (¬ p4390))
    : (¬ p4390) ∨ (¬ p2166) ∨ p2241 ∨ (¬ p2210) ∨ p2122 ∨ p2573 ∨ (¬ p3905) ∨ (¬ p3366) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4390 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4902 := h105456;
    (Or.elim h97437 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step124074 (p2210 p2363 p2470 p2528 p2881 p2891 p4503 p5193 : Prop)
    (h106530 : p4503)
    (h105488 : p5193)
    (h97444 : p2528 ∨ p2470 ∨ (¬ p2363) ∨ (¬ p4503) ∨ (¬ p2881) ∨ (¬ p5193) ∨ (¬ p2891) ∨ (¬ p2210))
    : p2528 ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2363) ∨ p2470 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4503 := h106530;
    let u7 : p5193 := h105488;
    (Or.elim h97444 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124075 (p2210 p2608 p2839 p4875 : Prop)
    (h106227 : p4875)
    (h97446 : p2608 ∨ (¬ p2210) ∨ p2839 ∨ (¬ p4875))
    : p2839 ∨ (¬ p2210) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4875 := h106227;
    (Or.elim h97446 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step124078 (p2122 p2210 p2241 p2396 p2744 p2774 p2972 p3366 p4395 : Prop)
    (h106503 : p2744)
    (h97451 : p2396 ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p4395) ∨ p2241 ∨ p2774 ∨ p2122)
    : (¬ p2210) ∨ p2122 ∨ (¬ p3366) ∨ p2774 ∨ p2396 ∨ (¬ p2972) ∨ p2241 ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h97451 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step124081 (p2210 p2363 p2774 p2819 p2891 p3246 p3950 p4736 : Prop)
    (h105431 : p4736)
    (h97462 : (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4736) ∨ (¬ p2210) ∨ p2363 ∨ (¬ p2891) ∨ p2819 ∨ p2774)
    : (¬ p2891) ∨ p2774 ∨ (¬ p2210) ∨ p2819 ∨ (¬ p3246) ∨ p2363 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97462 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124082 (p2210 p2352 p2553 p2774 p2819 p2881 p2891 p4736 : Prop)
    (h105431 : p4736)
    (h97469 : (¬ p2891) ∨ (¬ p2352) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p2881) ∨ (¬ p2210) ∨ p2819 ∨ p2553)
    : p2774 ∨ p2819 ∨ (¬ p2881) ∨ (¬ p2210) ∨ (¬ p2352) ∨ (¬ p2891) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97469 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (u6 r6)))))))))))))))))

theorem step124088 (p2166 p2210 p2254 p2651 p3016 p3146 p3564 p4604 : Prop)
    (h105366 : p2254)
    (h106293 : p4604)
    (h97481 : p3564 ∨ (¬ p3146) ∨ (¬ p4604) ∨ (¬ p2166) ∨ p2651 ∨ p3016 ∨ (¬ p2210) ∨ (¬ p2254))
    : (¬ p2166) ∨ p2651 ∨ (¬ p3146) ∨ p3564 ∨ (¬ p2210) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4604 := h106293;
    (Or.elim h97481 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124090 (p2166 p2210 p2598 p3146 p3422 p3564 p4604 p4736 : Prop)
    (h105431 : p4736)
    (h106293 : p4604)
    (h97484 : p3422 ∨ p3564 ∨ (¬ p3146) ∨ (¬ p4604) ∨ (¬ p2210) ∨ (¬ p2166) ∨ p2598 ∨ (¬ p4736))
    : p3422 ∨ p3564 ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p2166) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4604 := h106293;
    (Or.elim h97484 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124095 (p2264 p2573 p2807 p2881 p3201 p3422 p3905 p4647 p4786 : Prop)
    (h105412 : p4647)
    (h106425 : p4786)
    (h97498 : (¬ p2264) ∨ p2881 ∨ (¬ p4647) ∨ (¬ p3905) ∨ p2573 ∨ p3201 ∨ (¬ p2807) ∨ (¬ p4786) ∨ (¬ p3422))
    : (¬ p3422) ∨ p2573 ∨ (¬ p2807) ∨ p3201 ∨ (¬ p2264) ∨ p2881 ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4647 := h105412;
    let u8 : p4786 := h106425;
    (Or.elim h97498 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step124097 (p2210 p2651 p2911 p3201 p3366 p3399 p3631 p3683 p4236 p4377 p4668 : Prop)
    (h105414 : p4668)
    (h106170 : p4377)
    (h97501 : (¬ p3631) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4668) ∨ (¬ p4236) ∨ (¬ p3683) ∨ (¬ p4377) ∨ p2210 ∨ p3201 ∨ p2651 ∨ p2911)
    : p2210 ∨ p2651 ∨ (¬ p3399) ∨ (¬ p3631) ∨ p3201 ∨ p2911 ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3683) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4668 := h105414;
    let u10 : p4377 := h106170;
    (Or.elim h97501 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (u5 r9)))))))))))))))))))))))

theorem step124098 (p2727 p2996 p3201 p4066 p4279 p4750 : Prop)
    (h105433 : p4750)
    (h97503 : p2727 ∨ p2996 ∨ (¬ p4066) ∨ (¬ p4279) ∨ (¬ p4750) ∨ p3201)
    : (¬ p4066) ∨ p3201 ∨ (¬ p4279) ∨ p2727 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4066 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    (Or.elim h97503 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step124100 (p2210 p2417 p2598 p3201 p3366 p3399 p3527 p4377 p4666 : Prop)
    (h105658 : p4666)
    (h106170 : p4377)
    (h97505 : p2417 ∨ p2210 ∨ (¬ p4666) ∨ (¬ p4377) ∨ p3201 ∨ (¬ p3527) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p2598)
    : (¬ p3527) ∨ (¬ p3399) ∨ p3201 ∨ p2210 ∨ p2417 ∨ (¬ p3366) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    let u8 : p4377 := h106170;
    (Or.elim h97505 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u6 r7)))))))))))))))))))

theorem step124103 (p2187 p2192 p2210 p2598 p2911 p3201 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h97510 : p3201 ∨ (¬ p4736) ∨ p2911 ∨ (¬ p2187) ∨ p2598 ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4133))
    : p3201 ∨ (¬ p2210) ∨ (¬ p2192) ∨ p2598 ∨ p2911 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4133 := h105712;
    (Or.elim h97510 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124104 (p2241 p2449 p2598 p2911 p2996 p3201 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h97514 : (¬ p2449) ∨ p2996 ∨ (¬ p2241) ∨ (¬ p4668) ∨ p2911 ∨ p2598 ∨ p3201 ∨ (¬ p4736))
    : p2996 ∨ (¬ p2449) ∨ p3201 ∨ p2911 ∨ p2598 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4668 := h105414;
    (Or.elim h97514 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124105 (p2241 p2417 p2598 p2641 p3201 p3323 p4621 p4736 : Prop)
    (h105431 : p4736)
    (h105407 : p4621)
    (h97517 : p2417 ∨ (¬ p2641) ∨ p3201 ∨ (¬ p3323) ∨ (¬ p2241) ∨ (¬ p4621) ∨ p2598 ∨ (¬ p4736))
    : p3201 ∨ p2417 ∨ p2598 ∨ (¬ p2241) ∨ (¬ p3323) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4621 := h105407;
    (Or.elim h97517 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124107 (p2417 p2449 p3201 p3580 p4750 : Prop)
    (h105433 : p4750)
    (h97521 : p2417 ∨ (¬ p2449) ∨ (¬ p3580) ∨ p3201 ∨ (¬ p4750))
    : p3201 ∨ (¬ p2449) ∨ p2417 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h97521 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124109 (p2122 p2177 p2774 p3246 p3366 p3379 p3399 p3571 p4376 p4668 : Prop)
    (h105414 : p4668)
    (h106320 : p4376)
    (h97541 : (¬ p3246) ∨ p2774 ∨ p2177 ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p4668) ∨ (¬ p3571) ∨ p2122 ∨ p3379 ∨ (¬ p3399))
    : (¬ p3399) ∨ (¬ p3571) ∨ (¬ p3246) ∨ p3379 ∨ p2774 ∨ p2122 ∨ (¬ p3366) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4668 := h105414;
    let u9 : p4376 := h106320;
    (Or.elim h97541 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step124112 (p2241 p2685 p2751 p3037 p3399 : Prop)
    (h106343 : p2751)
    (h97546 : (¬ p3399) ∨ (¬ p3037) ∨ p2241 ∨ p2685 ∨ (¬ p2751))
    : p2685 ∨ (¬ p3399) ∨ (¬ p3037) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h97546 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124115 (p2230 p2264 p2274 p2563 p3399 p3527 p5193 : Prop)
    (h105488 : p5193)
    (h97564 : (¬ p3527) ∨ p2274 ∨ p2230 ∨ p2563 ∨ p2264 ∨ (¬ p3399) ∨ (¬ p5193))
    : p2563 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2274 ∨ p2230 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    (Or.elim h97564 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step124119 (p2241 p2352 p2363 p2573 p2744 p3366 p3399 p3631 p3905 p3950 : Prop)
    (h106503 : p2744)
    (h97573 : (¬ p3631) ∨ p2573 ∨ (¬ p3950) ∨ p2352 ∨ p2363 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3905) ∨ p2241 ∨ (¬ p2744))
    : (¬ p3631) ∨ (¬ p3399) ∨ p2241 ∨ (¬ p3905) ∨ p2573 ∨ p2363 ∨ (¬ p3366) ∨ (¬ p3950) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h97573 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124121 (p2598 p3276 p3399 p3527 p3941 p4736 p5119 p5160 : Prop)
    (h105431 : p4736)
    (h97581 : p3276 ∨ (¬ p3941) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4736) ∨ p2598 ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p5160) ∨ (¬ p3527) ∨ (¬ p3941) ∨ p2598 ∨ (¬ p3399) ∨ p3276 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97581 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124125 (p2459 p2598 p2850 p2982 p3399 p3527 p4736 p5059 : Prop)
    (h105431 : p4736)
    (h97587 : (¬ p3527) ∨ (¬ p4736) ∨ p2982 ∨ (¬ p3399) ∨ (¬ p5059) ∨ (¬ p2459) ∨ p2598 ∨ p2850)
    : p2850 ∨ (¬ p3527) ∨ p2982 ∨ (¬ p3399) ∨ p2598 ∨ (¬ p5059) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97587 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step124126 (p2459 p2598 p3399 p3422 p3527 p3564 p4604 p4736 : Prop)
    (h105431 : p4736)
    (h106293 : p4604)
    (h97590 : (¬ p3527) ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p2459) ∨ (¬ p4604) ∨ p3564 ∨ p3422 ∨ p2598)
    : (¬ p3527) ∨ (¬ p3399) ∨ p2598 ∨ p3564 ∨ (¬ p2459) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4604 := h106293;
    (Or.elim h97590 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step124128 (p2187 p2608 p3125 p3399 p3631 p3923 p4625 p4870 : Prop)
    (h106455 : p4625)
    (h97594 : p3125 ∨ (¬ p3399) ∨ p2608 ∨ (¬ p4625) ∨ (¬ p4870) ∨ (¬ p3631) ∨ (¬ p2187) ∨ (¬ p3923))
    : (¬ p3631) ∨ (¬ p3399) ∨ p2608 ∨ (¬ p2187) ∨ p3125 ∨ (¬ p3923) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4625 := h106455;
    (Or.elim h97594 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124132 (p2220 p2241 p2996 p3146 p3266 p3931 p4826 : Prop)
    (h105444 : p4826)
    (h97616 : (¬ p3931) ∨ p3146 ∨ p2220 ∨ (¬ p4826) ∨ (¬ p2241) ∨ p3266 ∨ p2996)
    : (¬ p3931) ∨ p2220 ∨ (¬ p2241) ∨ p3266 ∨ p3146 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4826 := h105444;
    (Or.elim h97616 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (u5 r5)))))))))))))))

theorem step124134 (p2132 p2241 p2750 p2753 p2860 p3073 p3125 p3449 p4330 : Prop)
    (h106345 : p2750)
    (h106329 : p4330)
    (h97624 : (¬ p3125) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p2750) ∨ p3449 ∨ (¬ p4330) ∨ p3073 ∨ (¬ p2241))
    : p3449 ∨ (¬ p2753) ∨ (¬ p2132) ∨ (¬ p3125) ∨ p3073 ∨ (¬ p2860) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p4330 := h106329;
    (Or.elim h97624 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124136 (p2156 p2192 p2241 p2750 p3369 p3371 : Prop)
    (h106345 : p2750)
    (h97631 : (¬ p3369) ∨ (¬ p3371) ∨ (¬ p2750) ∨ p2156 ∨ (¬ p2241) ∨ (¬ p2192))
    : (¬ p3369) ∨ (¬ p3371) ∨ p2156 ∨ (¬ p2192) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2750 := h106345;
    (Or.elim h97631 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step124137 (p2241 p2598 p3189 p3256 p3422 p3564 p4604 p4736 : Prop)
    (h105431 : p4736)
    (h106293 : p4604)
    (h97634 : (¬ p3256) ∨ (¬ p3189) ∨ (¬ p4736) ∨ (¬ p2241) ∨ p2598 ∨ p3422 ∨ (¬ p4604) ∨ p3564)
    : p3422 ∨ p3564 ∨ p2598 ∨ (¬ p3189) ∨ (¬ p2241) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4604 := h106293;
    (Or.elim h97634 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124138 (p2241 p2295 p2352 p2598 p2641 p3422 p4736 : Prop)
    (h105431 : p4736)
    (h97636 : (¬ p2641) ∨ (¬ p2295) ∨ p2352 ∨ p2598 ∨ (¬ p4736) ∨ p3422 ∨ (¬ p2241))
    : p2598 ∨ p3422 ∨ (¬ p2641) ∨ (¬ p2241) ∨ p2352 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    (Or.elim h97636 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step124141 (p2241 p2449 p2598 p2850 p2982 p2996 p3951 p4736 : Prop)
    (h105431 : p4736)
    (h106536 : p3951)
    (h97640 : p2982 ∨ (¬ p2449) ∨ p2850 ∨ (¬ p3951) ∨ (¬ p4736) ∨ p2996 ∨ (¬ p2241) ∨ p2598)
    : p2850 ∨ p2996 ∨ (¬ p2241) ∨ p2598 ∨ (¬ p2449) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p3951 := h106536;
    (Or.elim h97640 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step124145 (p2166 p2210 p2598 p3276 p3969 p4736 p5119 p5160 : Prop)
    (h105431 : p4736)
    (h97655 : (¬ p3969) ∨ p3276 ∨ (¬ p5160) ∨ (¬ p4736) ∨ (¬ p5119) ∨ p2598 ∨ (¬ p2210) ∨ (¬ p2166))
    : (¬ p3969) ∨ (¬ p5160) ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2598 ∨ p3276 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97655 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124146 (p2166 p2751 p3136 p3156 p4365 : Prop)
    (h106343 : p2751)
    (h97657 : (¬ p4365) ∨ (¬ p2751) ∨ (¬ p2166) ∨ p3136 ∨ p3156)
    : p3136 ∨ (¬ p2166) ∨ (¬ p4365) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h97657 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124148 (p2166 p2255 p2641 p2667 p2946 p3412 p3461 p3654 p3969 p5119 : Prop)
    (h105367 : p2255)
    (h97667 : p2641 ∨ p3461 ∨ (¬ p3412) ∨ (¬ p2255) ∨ p3654 ∨ (¬ p2166) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p5119) ∨ (¬ p3969))
    : (¬ p3969) ∨ (¬ p3412) ∨ p2641 ∨ p3461 ∨ p3654 ∨ (¬ p2667) ∨ (¬ p2166) ∨ (¬ p2946) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    (Or.elim h97667 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step124149 (p2166 p2210 p2437 p3146 p3343 p3389 p4697 p5193 : Prop)
    (h105488 : p5193)
    (h97670 : p3389 ∨ (¬ p3146) ∨ (¬ p2166) ∨ (¬ p4697) ∨ (¬ p2437) ∨ p3343 ∨ (¬ p5193) ∨ (¬ p2210))
    : p3389 ∨ (¬ p2437) ∨ (¬ p3146) ∨ p3343 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p4697) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h97670 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124153 (p2406 p2982 p3105 p3582 p5214 : Prop)
    (h105492 : p5214)
    (h97703 : (¬ p3105) ∨ (¬ p3582) ∨ p2406 ∨ (¬ p5214) ∨ p2982)
    : p2406 ∨ (¬ p3582) ∨ p2982 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5214 := h105492;
    (Or.elim h97703 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124154 (p2230 p2241 p2406 p2744 p4079 p4257 : Prop)
    (h106503 : p2744)
    (h97707 : p2241 ∨ (¬ p4257) ∨ (¬ p4079) ∨ (¬ p2744) ∨ (¬ p2230) ∨ p2406)
    : p2406 ∨ (¬ p2230) ∨ p2241 ∨ (¬ p4257) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2744 := h106503;
    (Or.elim h97707 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step124155 (p2230 p2406 p2829 p3759 p4257 p5224 : Prop)
    (h105494 : p5224)
    (h97708 : p2406 ∨ (¬ p2829) ∨ (¬ p2230) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p5224))
    : (¬ p2230) ∨ (¬ p2829) ∨ (¬ p3759) ∨ (¬ p4257) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5224 := h105494;
    (Or.elim h97708 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124156 (p2230 p2406 p3399 p4079 p4257 p4793 : Prop)
    (h105438 : p4793)
    (h97709 : p2406 ∨ p3399 ∨ (¬ p4257) ∨ (¬ p2230) ∨ (¬ p4793) ∨ (¬ p4079))
    : p2406 ∨ p3399 ∨ (¬ p2230) ∨ (¬ p4079) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4793 := h105438;
    (Or.elim h97709 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step124158 (p2696 p2972 p3425 p3434 p3461 p3590 p3680 p3948 p4621 p4749 : Prop)
    (h105432 : p4749)
    (h105407 : p4621)
    (h97722 : (¬ p3680) ∨ p3461 ∨ (¬ p3425) ∨ (¬ p4621) ∨ (¬ p4749) ∨ (¬ p3590) ∨ (¬ p3948) ∨ (¬ p2696) ∨ p3434 ∨ (¬ p2972))
    : (¬ p3680) ∨ (¬ p2972) ∨ (¬ p2696) ∨ (¬ p3425) ∨ (¬ p3948) ∨ p3434 ∨ (¬ p3590) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4749 := h105432;
    let u9 : p4621 := h105407;
    (Or.elim h97722 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step124159 (p2210 p2254 p2295 p2331 p2972 p3680 p4260 p4831 : Prop)
    (h105366 : p2254)
    (h105445 : p4831)
    (h97726 : (¬ p4260) ∨ p2331 ∨ p2295 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2972) ∨ (¬ p4831) ∨ (¬ p3680))
    : (¬ p4260) ∨ (¬ p3680) ∨ (¬ p2210) ∨ p2331 ∨ p2295 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4831 := h105445;
    (Or.elim h97726 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124166 (p2751 p2972 p3115 p3136 p4365 : Prop)
    (h106343 : p2751)
    (h97752 : (¬ p4365) ∨ p3115 ∨ (¬ p2972) ∨ p3136 ∨ (¬ p2751))
    : p3136 ∨ (¬ p2972) ∨ p3115 ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h97752 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124167 (p2264 p3032 p3146 p3631 p4443 p4902 : Prop)
    (h105456 : p4902)
    (h97766 : (¬ p3631) ∨ p3146 ∨ (¬ p4443) ∨ (¬ p4902) ∨ (¬ p3032) ∨ p2264)
    : (¬ p3631) ∨ p3146 ∨ (¬ p3032) ∨ p2264 ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4902 := h105456;
    (Or.elim h97766 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step124169 (p2927 p4647 p4914 : Prop)
    (h105412 : p4647)
    (h24424 : (¬ p2927) ∨ (¬ p4647) ∨ p4914)
    : (¬ p2927) ∨ p4914 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2927 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4914) := (fun h => hn (Or.inr h));
    let u2 : p4647 := h105412;
    (Or.elim h24424 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step124175 (p2241 p2459 p2992 p3156 p3367 p3537 p3609 p4902 : Prop)
    (h105456 : p4902)
    (h97787 : p3609 ∨ (¬ p2992) ∨ (¬ p2459) ∨ (¬ p3156) ∨ (¬ p3367) ∨ (¬ p4902) ∨ (¬ p2241) ∨ p3537)
    : p3537 ∨ (¬ p3156) ∨ (¬ p2992) ∨ p3609 ∨ (¬ p2459) ∨ (¬ p3367) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    (Or.elim h97787 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step124178 (p3319 p3367 p3483 p3953 p4426 p4752 : Prop)
    (h105434 : p4752)
    (h97798 : (¬ p3483) ∨ p3319 ∨ (¬ p4426) ∨ (¬ p4752) ∨ (¬ p3367) ∨ (¬ p3953))
    : (¬ p3953) ∨ (¬ p3483) ∨ (¬ p3367) ∨ (¬ p4426) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4752 := h105434;
    (Or.elim h97798 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step124179 (p2122 p2241 p2396 p2744 p2774 p3073 p3366 p3449 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h97821 : p2774 ∨ (¬ p3073) ∨ p2396 ∨ (¬ p4669) ∨ (¬ p2744) ∨ p2122 ∨ p2241 ∨ (¬ p3449) ∨ (¬ p3366))
    : (¬ p3449) ∨ p2241 ∨ p2396 ∨ p2774 ∨ p2122 ∨ (¬ p3073) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4669 := h105415;
    (Or.elim h97821 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124181 (p2122 p2307 p2786 p2946 p3146 p3156 p3483 p4330 p4789 : Prop)
    (h106329 : p4330)
    (h105646 : p4789)
    (h97826 : (¬ p2307) ∨ p3146 ∨ p3156 ∨ (¬ p2786) ∨ (¬ p3483) ∨ p2122 ∨ p2946 ∨ (¬ p4330) ∨ (¬ p4789))
    : (¬ p3483) ∨ (¬ p2786) ∨ (¬ p2307) ∨ p2946 ∨ p2122 ∨ p3146 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4330 := h106329;
    let u8 : p4789 := h105646;
    (Or.elim h97826 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124183 (p2122 p2177 p2319 p2341 p2788 : Prop)
    (h105375 : p2788)
    (h97835 : (¬ p2341) ∨ p2122 ∨ (¬ p2788) ∨ (¬ p2319) ∨ p2177)
    : (¬ p2319) ∨ (¬ p2341) ∨ p2122 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2788 := h105375;
    (Or.elim h97835 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124184 (p2122 p2295 p2383 p2819 p4581 : Prop)
    (h105405 : p4581)
    (h97839 : p2122 ∨ (¬ p2295) ∨ p2383 ∨ (¬ p2819) ∨ (¬ p4581))
    : p2122 ∨ (¬ p2819) ∨ (¬ p2295) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4581 := h105405;
    (Or.elim h97839 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124185 (p2122 p2315 p2341 p2819 p3550 : Prop)
    (h105368 : p2315)
    (h97845 : (¬ p2819) ∨ p2122 ∨ p2341 ∨ (¬ p2315) ∨ (¬ p3550))
    : (¬ p2819) ∨ p2341 ∨ p2122 ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2315 := h105368;
    (Or.elim h97845 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124188 (p2122 p2241 p2396 p2774 p2992 p3115 p4395 p4736 : Prop)
    (h105431 : p4736)
    (h97851 : (¬ p3115) ∨ (¬ p2992) ∨ (¬ p2241) ∨ p2774 ∨ p2396 ∨ (¬ p4395) ∨ p2122 ∨ (¬ p4736))
    : (¬ p3115) ∨ (¬ p2992) ∨ p2122 ∨ (¬ p2241) ∨ p2396 ∨ p2774 ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h97851 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124189 (p2122 p2177 p2230 p2406 p2518 p2774 p4079 p4420 p4736 : Prop)
    (h105431 : p4736)
    (h105707 : p4420)
    (h97852 : (¬ p2518) ∨ p2122 ∨ (¬ p4736) ∨ (¬ p4420) ∨ (¬ p2230) ∨ p2774 ∨ p2406 ∨ p2177 ∨ (¬ p4079))
    : (¬ p2518) ∨ p2406 ∨ p2774 ∨ (¬ p2230) ∨ p2177 ∨ (¬ p4079) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4420 := h105707;
    (Or.elim h97852 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124193 (p2122 p2774 p2946 p3115 p3680 p4260 p4786 p4831 : Prop)
    (h106425 : p4786)
    (h105445 : p4831)
    (h97863 : (¬ p3115) ∨ (¬ p4260) ∨ (¬ p2946) ∨ p2122 ∨ (¬ p4786) ∨ (¬ p4831) ∨ p2774 ∨ (¬ p3680))
    : (¬ p3680) ∨ (¬ p4260) ∨ p2122 ∨ (¬ p2946) ∨ p2774 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4831 := h105445;
    (Or.elim h97863 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124195 (p2122 p2307 p2373 p2440 p2651 p2786 p2819 p4134 p4789 : Prop)
    (h105379 : p4134)
    (h105646 : p4789)
    (h97867 : p2122 ∨ (¬ p2819) ∨ (¬ p4789) ∨ (¬ p4134) ∨ (¬ p2786) ∨ (¬ p2307) ∨ (¬ p2440) ∨ p2373 ∨ p2651)
    : (¬ p2819) ∨ p2651 ∨ p2122 ∨ (¬ p2440) ∨ (¬ p2786) ∨ p2373 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4134 := h105379;
    let u8 : p4789 := h105646;
    (Or.elim h97867 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step124196 (p2122 p2246 p2396 p2528 p2651 p2744 p2774 p3083 p3366 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h97868 : p2774 ∨ p2122 ∨ p2396 ∨ (¬ p3083) ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2651))
    : (¬ p3366) ∨ (¬ p2246) ∨ p2396 ∨ (¬ p3083) ∨ p2774 ∨ (¬ p2528) ∨ (¬ p2651) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3366 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4669 := h105415;
    (Or.elim h97868 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step124198 (p2122 p2230 p2774 p2982 p3680 p4260 p4419 p4831 : Prop)
    (h105445 : p4831)
    (h97877 : (¬ p4260) ∨ (¬ p3680) ∨ (¬ p4831) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p4419) ∨ p2122 ∨ p2774)
    : p2122 ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680) ∨ p2774 ∨ (¬ p4260) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    (Or.elim h97877 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124200 (p2122 p2396 p2774 p2881 p2901 p2946 p4666 p4786 : Prop)
    (h105658 : p4666)
    (h106425 : p4786)
    (h97879 : (¬ p2946) ∨ p2396 ∨ (¬ p2881) ∨ p2122 ∨ (¬ p4786) ∨ (¬ p2901) ∨ (¬ p4666) ∨ p2774)
    : p2774 ∨ p2122 ∨ (¬ p2881) ∨ p2396 ∨ (¬ p2946) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4666 := h105658;
    let u7 : p4786 := h106425;
    (Or.elim h97879 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step124201 (p2122 p2396 p2470 p2528 p2774 p3367 p3759 p4669 : Prop)
    (h105415 : p4669)
    (h97880 : p2774 ∨ (¬ p3367) ∨ (¬ p2470) ∨ p2396 ∨ p2122 ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p3759))
    : p2774 ∨ (¬ p3367) ∨ p2396 ∨ p2122 ∨ (¬ p3759) ∨ (¬ p2528) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h97880 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124203 (p2122 p2166 p2210 p2396 p2774 p3146 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h97883 : p2396 ∨ p2122 ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p4669) ∨ (¬ p2166) ∨ p2774 ∨ (¬ p4736))
    : p2774 ∨ (¬ p2166) ∨ (¬ p3146) ∨ p2122 ∨ p2396 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h97883 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124204 (p2122 p2210 p2396 p2774 p2881 p2891 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h97884 : (¬ p2881) ∨ p2396 ∨ (¬ p4736) ∨ p2774 ∨ p2122 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4666))
    : p2774 ∨ p2122 ∨ p2396 ∨ (¬ p2891) ∨ (¬ p2881) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h97884 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124205 (p2122 p2241 p2396 p2774 p3189 p3256 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h97885 : p2774 ∨ (¬ p3256) ∨ (¬ p3189) ∨ (¬ p2241) ∨ p2396 ∨ (¬ p4669) ∨ p2122 ∨ (¬ p4736))
    : p2774 ∨ (¬ p3189) ∨ p2122 ∨ (¬ p2241) ∨ p2396 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h97885 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124207 (p2122 p2177 p2655 p2774 p2946 p3156 p3367 p3759 p4902 : Prop)
    (h105456 : p4902)
    (h97893 : (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2946) ∨ p2774 ∨ (¬ p2655) ∨ (¬ p4902) ∨ p2177 ∨ p2122 ∨ (¬ p3156))
    : (¬ p2655) ∨ (¬ p3367) ∨ (¬ p2946) ∨ p2177 ∨ (¬ p3759) ∨ (¬ p3156) ∨ p2122 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    (Or.elim h97893 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124209 (p2088 p2122 p2177 p2331 p2482 p2528 p2630 p2656 p4328 p4420 : Prop)
    (h105707 : p4420)
    (h97896 : p2528 ∨ p2122 ∨ (¬ p2656) ∨ p2331 ∨ (¬ p4328) ∨ (¬ p4420) ∨ (¬ p2482) ∨ (¬ p2088) ∨ (¬ p2630) ∨ p2177)
    : (¬ p2482) ∨ p2331 ∨ (¬ p2088) ∨ (¬ p2656) ∨ p2528 ∨ p2177 ∨ p2122 ∨ (¬ p4328) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2482 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4420 := h105707;
    (Or.elim h97896 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step124210 (p2122 p2396 p2417 p3920 p5222 : Prop)
    (h105793 : p5222)
    (h97900 : (¬ p2417) ∨ (¬ p3920) ∨ p2396 ∨ p2122 ∨ (¬ p5222))
    : (¬ p2417) ∨ (¬ p3920) ∨ p2396 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5222 := h105793;
    (Or.elim h97900 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124215 (p2122 p2220 p2396 p2573 p3115 p3156 p3366 p3370 p3905 p4377 p4390 p4395 : Prop)
    (h106170 : p4377)
    (h97909 : (¬ p3115) ∨ p3156 ∨ (¬ p4377) ∨ p2122 ∨ p2573 ∨ (¬ p3370) ∨ p2396 ∨ (¬ p4395) ∨ (¬ p3905) ∨ (¬ p2220) ∨ (¬ p3366) ∨ (¬ p4390))
    : p2573 ∨ (¬ p2220) ∨ (¬ p4390) ∨ (¬ p3115) ∨ p2122 ∨ (¬ p3370) ∨ (¬ p3905) ∨ (¬ p3366) ∨ p3156 ∨ p2396 ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    (Or.elim h97909 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u9 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u2)))))))))))))))))))))))))

theorem step124217 (p2140 p2284 p2860 p2901 p3051 : Prop)
    (h105364 : p2140)
    (h97934 : (¬ p2901) ∨ p2284 ∨ p3051 ∨ (¬ p2860) ∨ (¬ p2140))
    : (¬ p2901) ∨ p2284 ∨ p3051 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h97934 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124218 (p2363 p2470 p2528 p2881 p2901 p2946 p3905 p4503 p4786 : Prop)
    (h106530 : p4503)
    (h106425 : p4786)
    (h97937 : (¬ p2901) ∨ (¬ p2881) ∨ (¬ p4503) ∨ p2528 ∨ (¬ p2946) ∨ p2470 ∨ (¬ p4786) ∨ (¬ p2363) ∨ (¬ p3905))
    : (¬ p2946) ∨ p2528 ∨ (¬ p2881) ∨ (¬ p2363) ∨ (¬ p2901) ∨ p2470 ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4503 := h106530;
    let u8 : p4786 := h106425;
    (Or.elim h97937 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124220 (p2331 p2901 p2946 p3745 p4558 : Prop)
    (h105400 : p4558)
    (h97943 : p2331 ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p4558) ∨ (¬ p3745))
    : p2331 ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h97943 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124221 (p2156 p2284 p2598 p2707 p2901 p3367 p3873 p4521 p4898 : Prop)
    (h105455 : p4898)
    (h97951 : (¬ p3367) ∨ (¬ p4898) ∨ (¬ p4521) ∨ p2707 ∨ (¬ p2901) ∨ (¬ p2156) ∨ p2284 ∨ (¬ p3873) ∨ p2598)
    : p2707 ∨ (¬ p3873) ∨ (¬ p2901) ∨ p2284 ∨ p2598 ∨ (¬ p2156) ∨ (¬ p3367) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4898 := h105455;
    (Or.elim h97951 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step124223 (p2901 p3125 p3323 p4153 p4558 : Prop)
    (h105400 : p4558)
    (h97962 : (¬ p3125) ∨ p3323 ∨ (¬ p4558) ∨ (¬ p2901) ∨ (¬ p4153))
    : (¬ p2901) ∨ (¬ p4153) ∨ p3323 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h97962 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124224 (p2383 p2668 p2901 p3743 p4153 p4558 : Prop)
    (h105400 : p4558)
    (h97963 : (¬ p2383) ∨ (¬ p4558) ∨ (¬ p3743) ∨ (¬ p2901) ∨ p2668 ∨ (¬ p4153))
    : (¬ p4153) ∨ (¬ p3743) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h97963 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step124226 (p2427 p2449 p3246 p4386 p4702 : Prop)
    (h106079 : p4702)
    (h97972 : (¬ p3246) ∨ p2449 ∨ (¬ p2427) ∨ (¬ p4702) ∨ (¬ p4386))
    : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p4386) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h97972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124227 (p2427 p2807 p2946 p3699 p4702 : Prop)
    (h106079 : p4702)
    (h97974 : (¬ p3699) ∨ (¬ p4702) ∨ (¬ p2427) ∨ p2807 ∨ (¬ p2946))
    : (¬ p2946) ∨ (¬ p3699) ∨ p2807 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h97974 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124228 (p2295 p2427 p2563 p4140 p4564 : Prop)
    (h105401 : p4564)
    (h97976 : (¬ p2427) ∨ p2295 ∨ p2563 ∨ (¬ p4564) ∨ (¬ p4140))
    : (¬ p2427) ∨ p2563 ∨ p2295 ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h97976 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124232 (p2156 p2264 p2427 p2563 p3399 p3527 p4362 p4521 : Prop)
    (h106173 : p4362)
    (h97991 : p3399 ∨ (¬ p2427) ∨ (¬ p4521) ∨ (¬ p2156) ∨ p3527 ∨ (¬ p2264) ∨ p2563 ∨ (¬ p4362))
    : p3527 ∨ p3399 ∨ (¬ p2427) ∨ (¬ p2264) ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4362 := h106173;
    (Or.elim h97991 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124233 (p2230 p2241 p2427 p2449 p2881 p2996 p4666 p5190 : Prop)
    (h105658 : p4666)
    (h105487 : p5190)
    (h97999 : (¬ p2996) ∨ p2241 ∨ (¬ p2881) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p4666) ∨ p2449 ∨ (¬ p2427))
    : (¬ p2996) ∨ p2241 ∨ p2449 ∨ (¬ p2881) ∨ (¬ p2230) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4666 := h105658;
    let u7 : p5190 := h105487;
    (Or.elim h97999 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124235 (p2177 p2264 p2437 p2440 p3016 p4711 : Prop)
    (h105655 : p4711)
    (h98009 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2264) ∨ (¬ p4711) ∨ p3016 ∨ p2177)
    : p3016 ∨ (¬ p2437) ∨ (¬ p2264) ∨ p2177 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4711 := h105655;
    (Or.elim h98009 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step124236 (p2249 p2437 p2727 p3389 : Prop)
    (h106513 : p2249)
    (h98011 : (¬ p2437) ∨ p3389 ∨ (¬ p2727) ∨ (¬ p2249))
    : p3389 ∨ (¬ p2437) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2249 := h106513;
    (Or.elim h98011 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step124238 (p2437 p3323 p3564 p3660 p4194 p4646 : Prop)
    (h105534 : p4646)
    (h98017 : (¬ p3564) ∨ p3323 ∨ (¬ p4646) ∨ (¬ p4194) ∨ (¬ p3660) ∨ (¬ p2437))
    : (¬ p2437) ∨ (¬ p4194) ∨ (¬ p3660) ∨ (¬ p3564) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4646 := h105534;
    (Or.elim h98017 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step124239 (p2156 p2187 p2363 p2417 p2437 p2651 p2753 p3645 p3950 p4117 p4877 : Prop)
    (h105451 : p4877)
    (h98018 : (¬ p4877) ∨ p2363 ∨ (¬ p2417) ∨ p2187 ∨ (¬ p3950) ∨ (¬ p4117) ∨ (¬ p3645) ∨ (¬ p2651) ∨ p2156 ∨ (¬ p2437) ∨ (¬ p2753))
    : (¬ p4117) ∨ (¬ p2753) ∨ p2187 ∨ (¬ p3950) ∨ p2363 ∨ (¬ p2651) ∨ (¬ p2437) ∨ (¬ p3645) ∨ (¬ p2417) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4877 := h105451;
    (Or.elim h98018 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step124240 (p2230 p2437 p2850 p3389 p4750 : Prop)
    (h105433 : p4750)
    (h98022 : p2850 ∨ (¬ p2230) ∨ (¬ p4750) ∨ (¬ p2437) ∨ p3389)
    : p2850 ∨ p3389 ∨ (¬ p2230) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h98022 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step124241 (p2230 p2406 p2437 p3389 p4811 : Prop)
    (h105633 : p4811)
    (h98026 : (¬ p2437) ∨ (¬ p4811) ∨ (¬ p2230) ∨ p3389 ∨ p2406)
    : p3389 ∨ (¬ p2230) ∨ p2406 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h98026 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124243 (p2437 p2651 p2946 p3879 p4646 : Prop)
    (h105534 : p4646)
    (h98032 : p2946 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p4646) ∨ (¬ p3879))
    : p2946 ∨ (¬ p3879) ∨ (¬ p2437) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h98032 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124244 (p2437 p3083 p3516 p3575 p4383 p4668 : Prop)
    (h105414 : p4668)
    (h98034 : (¬ p3516) ∨ p3083 ∨ (¬ p3575) ∨ (¬ p4668) ∨ (¬ p2437) ∨ (¬ p4383))
    : (¬ p3516) ∨ (¬ p3575) ∨ (¬ p4383) ∨ p3083 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4668 := h105414;
    (Or.elim h98034 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step124245 (p2252 p2437 p2608 p2655 p2750 p3083 p3093 p3319 p3389 p3461 : Prop)
    (h106345 : p2750)
    (h98036 : p2608 ∨ (¬ p2655) ∨ (¬ p2252) ∨ (¬ p3461) ∨ p3389 ∨ p3083 ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p2750) ∨ (¬ p2437))
    : (¬ p3319) ∨ (¬ p2437) ∨ p2608 ∨ p3389 ∨ (¬ p3093) ∨ (¬ p3461) ∨ p3083 ∨ (¬ p2655) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    (Or.elim h98036 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step124246 (p2331 p2437 p2655 p3389 p4975 : Prop)
    (h105464 : p4975)
    (h98041 : (¬ p2437) ∨ (¬ p2331) ∨ p3389 ∨ (¬ p2655) ∨ (¬ p4975))
    : p3389 ∨ (¬ p2655) ∨ (¬ p2331) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h98041 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124248 (p2248 p2437 p2608 p2651 p2707 p2911 p3434 p4666 : Prop)
    (h105365 : p2248)
    (h105658 : p4666)
    (h98051 : p2707 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p2911) ∨ p3434 ∨ (¬ p4666) ∨ (¬ p2437))
    : p2707 ∨ p3434 ∨ p2608 ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4666 := h105658;
    (Or.elim h98051 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124251 (p2383 p2437 p2578 p2668 p4194 p4711 : Prop)
    (h105655 : p4711)
    (h98063 : (¬ p2383) ∨ (¬ p2578) ∨ (¬ p4194) ∨ (¬ p4711) ∨ (¬ p2437) ∨ p2668)
    : (¬ p2578) ∨ (¬ p2383) ∨ (¬ p2437) ∨ p2668 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2578 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4711 := h105655;
    (Or.elim h98063 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step124254 (p2437 p2727 p2992 p3879 p4646 : Prop)
    (h105534 : p4646)
    (h98069 : p2992 ∨ (¬ p2437) ∨ (¬ p3879) ∨ (¬ p4646) ∨ (¬ p2727))
    : p2992 ∨ (¬ p3879) ∨ (¬ p2437) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h98069 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124257 (p2437 p2911 p2926 p3527 p4811 : Prop)
    (h105633 : p4811)
    (h98075 : p3527 ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p2926) ∨ (¬ p4811))
    : (¬ p2926) ∨ p3527 ∨ (¬ p2911) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2926 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h98075 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124258 (p2246 p2383 p2417 p2437 p2651 p2744 p2778 p2819 p3366 p3917 p4625 : Prop)
    (h106503 : p2744)
    (h106455 : p4625)
    (h98076 : (¬ p3917) ∨ (¬ p2819) ∨ (¬ p4625) ∨ (¬ p2417) ∨ p2383 ∨ (¬ p2778) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2651))
    : (¬ p2819) ∨ (¬ p2417) ∨ (¬ p3917) ∨ (¬ p2246) ∨ (¬ p2778) ∨ (¬ p2437) ∨ p2383 ∨ (¬ p2651) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4625 := h106455;
    (Or.elim h98076 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step124261 (p2417 p2437 p2926 p3631 p4811 : Prop)
    (h105633 : p4811)
    (h98079 : (¬ p2417) ∨ p3631 ∨ (¬ p4811) ∨ (¬ p2926) ∨ (¬ p2437))
    : (¬ p2926) ∨ (¬ p2417) ∨ p3631 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2926 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h98079 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124263 (p2145 p2187 p2383 p2417 p2437 p2651 p3125 p4117 p4198 p4625 : Prop)
    (h106455 : p4625)
    (h98083 : (¬ p2145) ∨ (¬ p4117) ∨ (¬ p2417) ∨ (¬ p4625) ∨ (¬ p2437) ∨ p2383 ∨ (¬ p4198) ∨ p3125 ∨ (¬ p2187) ∨ (¬ p2651))
    : (¬ p4117) ∨ (¬ p2187) ∨ (¬ p4198) ∨ p3125 ∨ (¬ p2417) ∨ p2383 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4625 := h106455;
    (Or.elim h98083 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step124266 (p2331 p2440 p2651 p4717 : Prop)
    (h105424 : p4717)
    (h98102 : (¬ p2331) ∨ (¬ p2440) ∨ p2651 ∨ (¬ p4717))
    : p2651 ∨ (¬ p2440) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4717 := h105424;
    (Or.elim h98102 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step124268 (p2651 p2685 p2727 p2751 p2807 : Prop)
    (h106343 : p2751)
    (h98111 : (¬ p2727) ∨ (¬ p2751) ∨ (¬ p2807) ∨ p2651 ∨ p2685)
    : p2685 ∨ p2651 ∨ (¬ p2807) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h98111 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124269 (p2295 p2312 p2651 p4975 : Prop)
    (h105464 : p4975)
    (h98112 : p2295 ∨ p2312 ∨ (¬ p4975) ∨ p2651)
    : p2312 ∨ p2651 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2312) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4975 := h105464;
    (Or.elim h98112 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step124271 (p2139 p2177 p2630 p2651 p2685 p2881 p3051 p4236 p4361 : Prop)
    (h105382 : p4361)
    (h98114 : (¬ p2881) ∨ p2177 ∨ (¬ p4236) ∨ (¬ p2139) ∨ p2651 ∨ p2685 ∨ (¬ p3051) ∨ (¬ p2630) ∨ (¬ p4361))
    : (¬ p2630) ∨ p2685 ∨ (¬ p4236) ∨ (¬ p2881) ∨ p2177 ∨ (¬ p3051) ∨ p2651 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4361 := h105382;
    (Or.elim h98114 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124272 (p2264 p2341 p2651 p4067 p4104 p4975 : Prop)
    (h105464 : p4975)
    (h98115 : (¬ p2341) ∨ (¬ p4067) ∨ (¬ p4104) ∨ (¬ p4975) ∨ p2651 ∨ p2264)
    : (¬ p2341) ∨ p2651 ∨ (¬ p4104) ∨ (¬ p4067) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h98115 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step124274 (p2252 p2528 p2651 p2750 p2761 p3083 p3599 p3670 p3950 : Prop)
    (h106345 : p2750)
    (h98121 : (¬ p3599) ∨ p2761 ∨ p2651 ∨ (¬ p3670) ∨ p3083 ∨ (¬ p2750) ∨ (¬ p3950) ∨ (¬ p2252) ∨ p2528)
    : (¬ p3670) ∨ (¬ p3599) ∨ p2761 ∨ p2528 ∨ p2651 ∨ p3083 ∨ (¬ p2252) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    (Or.elim h98121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step124275 (p2192 p2210 p2254 p2528 p2651 p3083 p3125 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h98122 : (¬ p3125) ∨ p2528 ∨ (¬ p2192) ∨ (¬ p2254) ∨ (¬ p2210) ∨ p3083 ∨ (¬ p4330) ∨ p2651)
    : p3083 ∨ p2651 ∨ (¬ p3125) ∨ (¬ p2210) ∨ p2528 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h98122 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124276 (p2210 p2528 p2651 p3083 p3366 p3399 p3631 p3950 p4236 p4377 : Prop)
    (h106170 : p4377)
    (h98123 : (¬ p3631) ∨ p2210 ∨ (¬ p3399) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p4377) ∨ p3083 ∨ p2651 ∨ p2528)
    : p2651 ∨ p2210 ∨ (¬ p4236) ∨ (¬ p3399) ∨ (¬ p3950) ∨ p2528 ∨ p3083 ∨ (¬ p3631) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    (Or.elim h98123 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step124278 (p2341 p2651 p2881 p3246 p3366 p3370 p3422 p3564 p3683 p4236 p4377 p4625 p4988 : Prop)
    (h106170 : p4377)
    (h106455 : p4625)
    (h98138 : (¬ p3370) ∨ p3422 ∨ p2651 ∨ p2881 ∨ (¬ p4988) ∨ p3564 ∨ (¬ p3683) ∨ (¬ p4625) ∨ (¬ p4236) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p4377))
    : (¬ p3366) ∨ p2651 ∨ (¬ p3683) ∨ p2881 ∨ p3564 ∨ (¬ p2341) ∨ (¬ p4988) ∨ p3422 ∨ (¬ p3370) ∨ (¬ p3246) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3366 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    let u12 : p4625 := h106455;
    (Or.elim h98138 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u0))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step124282 (p2210 p2252 p2417 p2437 p2651 p2881 p3399 p3571 p4448 p4666 : Prop)
    (h105658 : p4666)
    (h98152 : p2417 ∨ p2210 ∨ p2437 ∨ (¬ p3571) ∨ (¬ p3399) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p4666) ∨ (¬ p4448) ∨ (¬ p2881))
    : p2651 ∨ p2210 ∨ (¬ p3399) ∨ (¬ p3571) ∨ p2417 ∨ (¬ p2881) ∨ p2437 ∨ (¬ p4448) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4666 := h105658;
    (Or.elim h98152 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step124283 (p2210 p2254 p2417 p2437 p2651 p2881 p2891 p4666 : Prop)
    (h105366 : p2254)
    (h105658 : p4666)
    (h98153 : p2437 ∨ p2651 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4666) ∨ (¬ p2881) ∨ (¬ p2254) ∨ p2417)
    : p2651 ∨ p2437 ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p2881) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4666 := h105658;
    (Or.elim h98153 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step124284 (p2331 p2493 p2651 p3984 p4811 : Prop)
    (h105633 : p4811)
    (h98155 : (¬ p2331) ∨ (¬ p4811) ∨ (¬ p3984) ∨ p2493 ∨ p2651)
    : p2651 ∨ p2493 ∨ (¬ p2331) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h98155 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124286 (p2449 p2651 p3516 p4067 p4104 p4975 : Prop)
    (h105464 : p4975)
    (h98171 : (¬ p3516) ∨ p2449 ∨ p2651 ∨ (¬ p4067) ∨ (¬ p4104) ∨ (¬ p4975))
    : p2651 ∨ (¬ p3516) ∨ p2449 ∨ (¬ p4104) ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h98171 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124289 (p2166 p2210 p2254 p2651 p3276 p3343 p3969 p5119 : Prop)
    (h105366 : p2254)
    (h98186 : (¬ p3969) ∨ p3276 ∨ (¬ p2210) ∨ p2651 ∨ p3343 ∨ (¬ p5119) ∨ (¬ p2254) ∨ (¬ p2166))
    : (¬ p3969) ∨ (¬ p2166) ∨ p2651 ∨ (¬ p5119) ∨ p3343 ∨ p3276 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h98186 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124294 (p2156 p2187 p2363 p2598 p3016 p3343 p3366 p3370 p4377 p5160 : Prop)
    (h106170 : p4377)
    (h98210 : (¬ p5160) ∨ (¬ p3343) ∨ (¬ p2156) ∨ (¬ p3370) ∨ p2598 ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p2187) ∨ p3016 ∨ (¬ p4377))
    : p2598 ∨ (¬ p3366) ∨ (¬ p2156) ∨ (¬ p3343) ∨ (¬ p3370) ∨ (¬ p2363) ∨ p3016 ∨ (¬ p2187) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    (Or.elim h98210 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124295 (p2156 p2960 p3125 p3323 p4153 : Prop)
    (h105377 : p2960)
    (h98211 : (¬ p3125) ∨ p3323 ∨ (¬ p2156) ∨ (¬ p4153) ∨ (¬ p2960))
    : (¬ p2156) ∨ (¬ p4153) ∨ (¬ p3125) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2960 := h105377;
    (Or.elim h98211 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124298 (p2249 p2331 p2396 p2881 p2951 p2992 p3051 p3309 p3922 p4666 : Prop)
    (h105658 : p4666)
    (h106513 : p2249)
    (h98216 : (¬ p2881) ∨ p2396 ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2249) ∨ (¬ p3922) ∨ (¬ p4666) ∨ p2331 ∨ p3309 ∨ (¬ p2951))
    : p2331 ∨ (¬ p2951) ∨ (¬ p2881) ∨ p2396 ∨ (¬ p3051) ∨ (¬ p2992) ∨ p3309 ∨ (¬ p3922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    let u9 : p2249 := h106513;
    (Or.elim h98216 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step124302 (p2264 p2881 p2960 p3051 : Prop)
    (h105377 : p2960)
    (h98222 : (¬ p2881) ∨ (¬ p3051) ∨ p2264 ∨ (¬ p2960))
    : (¬ p2881) ∨ (¬ p3051) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2960 := h105377;
    (Or.elim h98222 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step124304 (p2331 p2363 p2427 p2668 p2982 p3051 p3366 p3519 p4236 p4376 p4399 p4450 : Prop)
    (h106320 : p4376)
    (h98225 : p2331 ∨ (¬ p3051) ∨ p2668 ∨ (¬ p3519) ∨ (¬ p2982) ∨ (¬ p4399) ∨ (¬ p4450) ∨ p2427 ∨ p2363 ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p4236))
    : p2331 ∨ (¬ p3519) ∨ (¬ p3051) ∨ (¬ p4399) ∨ p2363 ∨ (¬ p4450) ∨ (¬ p3366) ∨ (¬ p2982) ∨ p2427 ∨ (¬ p4236) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4376 := h106320;
    (Or.elim h98225 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u10 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u9)))))))))))))))))))))))))

theorem step124306 (p2449 p2960 p3051 p3246 p4386 : Prop)
    (h105377 : p2960)
    (h98237 : (¬ p3246) ∨ p2449 ∨ (¬ p3051) ∨ (¬ p2960) ∨ (¬ p4386))
    : (¬ p3051) ∨ (¬ p4386) ∨ p2449 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2960 := h105377;
    (Or.elim h98237 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124308 (p2156 p2295 p3051 p4140 p4564 : Prop)
    (h105401 : p4564)
    (h98248 : (¬ p3051) ∨ (¬ p4140) ∨ p2156 ∨ (¬ p4564) ∨ p2295)
    : (¬ p3051) ∨ p2156 ∨ (¬ p4140) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h98248 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124309 (p2274 p2284 p2553 p2590 p4705 : Prop)
    (h106238 : p4705)
    (h98283 : p2553 ∨ (¬ p2274) ∨ (¬ p4705) ∨ (¬ p2284) ∨ (¬ p2590))
    : (¬ p2284) ∨ p2553 ∨ (¬ p2274) ∨ (¬ p2590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h98283 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124310 (p2352 p2553 p2881 p3550 p4556 : Prop)
    (h105399 : p4556)
    (h98287 : (¬ p2352) ∨ (¬ p3550) ∨ p2553 ∨ p2881 ∨ (¬ p4556))
    : (¬ p2352) ∨ (¬ p3550) ∨ p2881 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    (Or.elim h98287 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124311 (p2352 p2396 p2553 p3550 p4666 : Prop)
    (h105658 : p4666)
    (h98288 : (¬ p2352) ∨ p2553 ∨ p2396 ∨ (¬ p4666) ∨ (¬ p3550))
    : p2553 ∨ (¬ p2352) ∨ (¬ p3550) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h98288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124315 (p2307 p2386 p3016 p3083 p4157 p4405 : Prop)
    (h105512 : p4405)
    (h98314 : (¬ p4157) ∨ p3016 ∨ (¬ p4405) ∨ (¬ p2386) ∨ (¬ p3083) ∨ p2307)
    : (¬ p4157) ∨ (¬ p3083) ∨ p2307 ∨ p3016 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4157 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    (Or.elim h98314 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step124317 (p2307 p2396 p2518 p2528 p2598 p2785 p2829 p3590 p4669 : Prop)
    (h105415 : p4669)
    (h98331 : p2829 ∨ p2307 ∨ (¬ p4669) ∨ (¬ p2785) ∨ (¬ p2528) ∨ (¬ p3590) ∨ p2396 ∨ (¬ p2518) ∨ (¬ p2598))
    : (¬ p2785) ∨ (¬ p2598) ∨ p2307 ∨ (¬ p2518) ∨ p2396 ∨ (¬ p2528) ∨ (¬ p3590) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h98331 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step124319 (p2140 p2274 p2307 p2860 p4198 : Prop)
    (h105364 : p2140)
    (h98333 : p2307 ∨ (¬ p2274) ∨ (¬ p4198) ∨ (¬ p2860) ∨ (¬ p2140))
    : (¬ p4198) ∨ (¬ p2860) ∨ p2307 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h98333 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124320 (p2307 p2396 p2417 p2581 p3920 : Prop)
    (h105371 : p2581)
    (h98336 : (¬ p2417) ∨ p2307 ∨ (¬ p3920) ∨ p2396 ∨ (¬ p2581))
    : (¬ p2417) ∨ (¬ p3920) ∨ p2307 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2581 := h105371;
    (Or.elim h98336 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124321 (p2122 p2307 p2778 p3146 p3166 p3256 p3917 p3990 p4433 p4786 : Prop)
    (h106150 : p4433)
    (h106425 : p4786)
    (h98340 : p2307 ∨ (¬ p2122) ∨ (¬ p3990) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p4433) ∨ (¬ p2778) ∨ p3146 ∨ (¬ p3917) ∨ (¬ p4786))
    : (¬ p2122) ∨ (¬ p3917) ∨ p3146 ∨ p2307 ∨ (¬ p3990) ∨ (¬ p3256) ∨ (¬ p2778) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4433 := h106150;
    let u9 : p4786 := h106425;
    (Or.elim h98340 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124323 (p2307 p2383 p2396 p3550 p4666 : Prop)
    (h105658 : p4666)
    (h98348 : (¬ p3550) ∨ p2396 ∨ (¬ p4666) ∨ p2307 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2307 ∨ p2396 ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h98348 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124325 (p2187 p2241 p2274 p2307 p2608 p3189 p3645 p4198 p4771 p4877 : Prop)
    (h105451 : p4877)
    (h98351 : p2608 ∨ (¬ p3189) ∨ (¬ p4198) ∨ (¬ p2241) ∨ p2187 ∨ (¬ p3645) ∨ (¬ p4771) ∨ p2307 ∨ (¬ p4877) ∨ (¬ p2274))
    : (¬ p3189) ∨ (¬ p2241) ∨ (¬ p4771) ∨ (¬ p4198) ∨ p2307 ∨ (¬ p3645) ∨ p2187 ∨ (¬ p2274) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    (Or.elim h98351 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step124327 (p2274 p2307 p2383 p2668 p4564 : Prop)
    (h105401 : p4564)
    (h98359 : (¬ p2383) ∨ (¬ p2274) ∨ p2307 ∨ p2668 ∨ (¬ p4564))
    : (¬ p2383) ∨ (¬ p2274) ∨ p2668 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h98359 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124333 (p2352 p2383 p2427 p3660 p4356 p4555 : Prop)
    (h105542 : p4555)
    (h98387 : p2427 ∨ (¬ p2352) ∨ (¬ p4356) ∨ p2383 ∨ (¬ p3660) ∨ (¬ p4555))
    : p2383 ∨ (¬ p2352) ∨ (¬ p4356) ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h98387 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124334 (p2255 p2383 p2641 p2667 p2946 p2972 p3412 p3680 p5123 p5580 : Prop)
    (h105367 : p2255)
    (h98392 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3680) ∨ (¬ p2255) ∨ p2383 ∨ (¬ p2946) ∨ (¬ p2667) ∨ p2641 ∨ (¬ p3412) ∨ (¬ p2972))
    : (¬ p3680) ∨ (¬ p5580) ∨ (¬ p5123) ∨ p2383 ∨ (¬ p3412) ∨ p2641 ∨ (¬ p2667) ∨ (¬ p2972) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    (Or.elim h98392 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step124335 (p2140 p2187 p2383 p2860 p4198 : Prop)
    (h105364 : p2140)
    (h98394 : (¬ p2187) ∨ (¬ p2860) ∨ (¬ p4198) ∨ (¬ p2140) ∨ p2383)
    : (¬ p2860) ∨ (¬ p2187) ∨ (¬ p4198) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h98394 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124336 (p2143 p2187 p2383 p2870 p4198 p4558 : Prop)
    (h105400 : p4558)
    (h98395 : (¬ p2143) ∨ (¬ p2187) ∨ p2383 ∨ (¬ p4558) ∨ (¬ p4198) ∨ (¬ p2870))
    : p2383 ∨ (¬ p2187) ∨ (¬ p2870) ∨ (¬ p4198) ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h98395 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step124339 (p2088 p2651 p3170 p3256 p5008 : Prop)
    (h105469 : p5008)
    (h98423 : (¬ p3170) ∨ (¬ p3256) ∨ (¬ p5008) ∨ (¬ p2651) ∨ p2088)
    : (¬ p3170) ∨ p2088 ∨ (¬ p2651) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3170 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5008 := h105469;
    (Or.elim h98423 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step124344 (p2088 p2331 p3170 p3256 p4121 p4975 : Prop)
    (h105464 : p4975)
    (h98446 : (¬ p4121) ∨ (¬ p3170) ∨ p2088 ∨ (¬ p3256) ∨ (¬ p2331) ∨ (¬ p4975))
    : (¬ p4121) ∨ (¬ p3170) ∨ p2088 ∨ (¬ p3256) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4121 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h98446 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124347 (p2383 p2497 p2578 p3422 p3923 p5214 : Prop)
    (h105492 : p5214)
    (h57891 : (¬ p2383) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3923) ∨ (¬ p5214))
    : (¬ p3422) ∨ (¬ p2383) ∨ (¬ p2578) ∨ (¬ p2497) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5214 := h105492;
    (Or.elim h57891 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124351 (p2254 p2274 p2284 p2352 p2493 p2946 p3379 p4405 : Prop)
    (h105512 : p4405)
    (h105366 : p2254)
    (h98505 : (¬ p2493) ∨ (¬ p2352) ∨ p2274 ∨ (¬ p2254) ∨ p2284 ∨ (¬ p3379) ∨ p2946 ∨ (¬ p4405))
    : (¬ p2493) ∨ (¬ p2352) ∨ p2274 ∨ p2946 ∨ (¬ p3379) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : p2254 := h105366;
    (Or.elim h98505 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124353 (p2274 p2352 p2528 p3146 p3955 p4718 : Prop)
    (h105425 : p4718)
    (h98515 : (¬ p2528) ∨ (¬ p2352) ∨ (¬ p3955) ∨ (¬ p4718) ∨ p2274 ∨ p3146)
    : (¬ p2352) ∨ (¬ p2528) ∨ p2274 ∨ (¬ p3955) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4718 := h105425;
    (Or.elim h98515 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step124355 (p2881 p3941 p3955 p4559 p5580 : Prop)
    (h105701 : p4559)
    (h41328 : (¬ p2881) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p4559) ∨ (¬ p5580))
    : (¬ p3941) ∨ (¬ p5580) ∨ (¬ p3955) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4559 := h105701;
    (Or.elim h41328 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124356 (p2264 p2363 p2459 p3955 p4361 : Prop)
    (h105382 : p4361)
    (h98518 : (¬ p2264) ∨ (¬ p4361) ∨ (¬ p3955) ∨ (¬ p2459) ∨ p2363)
    : p2363 ∨ (¬ p2264) ∨ (¬ p3955) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4361 := h105382;
    (Or.elim h98518 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124361 (p2255 p2383 p2641 p2668 p3987 : Prop)
    (h105367 : p2255)
    (h98544 : (¬ p2383) ∨ p2668 ∨ (¬ p3987) ∨ p2641 ∨ (¬ p2255))
    : (¬ p2383) ∨ p2641 ∨ (¬ p3987) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h98544 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124362 (p2187 p2373 p2668 p4702 : Prop)
    (h106079 : p4702)
    (h98552 : (¬ p2373) ∨ p2668 ∨ (¬ p4702) ∨ (¬ p2187))
    : (¬ p2373) ∨ (¬ p2187) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4702 := h106079;
    (Or.elim h98552 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step124363 (p2252 p2331 p2598 p2668 p2748 p3366 p3537 p3609 p4749 p5118 p5580 : Prop)
    (h105432 : p4749)
    (h105482 : p5118)
    (h98555 : (¬ p5580) ∨ (¬ p3609) ∨ (¬ p2748) ∨ (¬ p2252) ∨ p2331 ∨ (¬ p3537) ∨ (¬ p3366) ∨ p2598 ∨ p2668 ∨ (¬ p5118) ∨ (¬ p4749))
    : (¬ p3609) ∨ (¬ p3537) ∨ (¬ p5580) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3366) ∨ p2668 ∨ p2331 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4749 := h105432;
    let u10 : p5118 := h105482;
    (Or.elim h98555 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step124364 (p2210 p2254 p2331 p2668 p2972 p3680 p5123 p5580 : Prop)
    (h105366 : p2254)
    (h98565 : (¬ p5580) ∨ (¬ p3680) ∨ p2668 ∨ (¬ p2972) ∨ p2331 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p5123))
    : (¬ p3680) ∨ (¬ p5580) ∨ (¬ p2972) ∨ p2668 ∨ (¬ p2210) ∨ p2331 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h98565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124365 (p2210 p2254 p2331 p2363 p2668 p2891 p3246 p3950 : Prop)
    (h105366 : p2254)
    (h98567 : p2363 ∨ (¬ p3246) ∨ p2331 ∨ p2668 ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3950))
    : (¬ p2891) ∨ p2331 ∨ (¬ p3246) ∨ p2668 ∨ (¬ p3950) ∨ (¬ p2210) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h98567 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124366 (p2187 p2563 p2668 p4153 p4702 : Prop)
    (h106079 : p4702)
    (h98572 : p2668 ∨ (¬ p2187) ∨ (¬ p4702) ∨ (¬ p2563) ∨ (¬ p4153))
    : (¬ p4153) ∨ (¬ p2187) ∨ p2668 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h98572 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124367 (p2098 p2331 p2668 p4236 p4503 p4804 : Prop)
    (h106530 : p4503)
    (h98577 : (¬ p4236) ∨ (¬ p2098) ∨ (¬ p4804) ∨ p2668 ∨ (¬ p4503) ∨ p2331)
    : p2331 ∨ (¬ p4804) ∨ p2668 ∨ (¬ p2098) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4503 := h106530;
    (Or.elim h98577 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step124368 (p2139 p2373 p2427 p2668 p2696 p2797 p3051 p4433 : Prop)
    (h106150 : p4433)
    (h98578 : p2797 ∨ p2668 ∨ (¬ p2139) ∨ (¬ p2373) ∨ (¬ p4433) ∨ p2696 ∨ (¬ p3051) ∨ p2427)
    : (¬ p3051) ∨ p2797 ∨ (¬ p2139) ∨ p2668 ∨ p2427 ∨ (¬ p2373) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4433 := h106150;
    (Or.elim h98578 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124369 (p2331 p2363 p2668 p3366 p3379 p3449 p4181 p4236 p4376 p5122 : Prop)
    (h106320 : p4376)
    (h105483 : p5122)
    (h98582 : (¬ p4181) ∨ p2331 ∨ p3379 ∨ (¬ p4236) ∨ p2363 ∨ p2668 ∨ (¬ p5122) ∨ (¬ p3449) ∨ (¬ p4376) ∨ (¬ p3366))
    : (¬ p4181) ∨ p2331 ∨ p2363 ∨ (¬ p3449) ∨ p3379 ∨ (¬ p3366) ∨ p2668 ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5122 := h105483;
    (Or.elim h98582 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step124375 (p2177 p2295 p2881 p3872 p4564 : Prop)
    (h105401 : p4564)
    (h98614 : (¬ p2881) ∨ p2295 ∨ p2177 ∨ (¬ p3872) ∨ (¬ p4564))
    : (¬ p3872) ∨ p2177 ∨ (¬ p2881) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3872 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h98614 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124376 (p2295 p2396 p3246 p3872 p4564 : Prop)
    (h105401 : p4564)
    (h98617 : (¬ p3246) ∨ p2295 ∨ (¬ p3872) ∨ p2396 ∨ (¬ p4564))
    : (¬ p3246) ∨ p2396 ∨ p2295 ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h98617 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124377 (p2274 p2295 p3156 p4153 p4509 : Prop)
    (h105392 : p4509)
    (h98630 : p2295 ∨ (¬ p2274) ∨ (¬ p4153) ∨ (¬ p4509) ∨ (¬ p3156))
    : (¬ p3156) ∨ (¬ p4153) ∨ p2295 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h98630 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124378 (p2274 p2295 p2563 p4153 p4702 : Prop)
    (h106079 : p4702)
    (h98631 : (¬ p4153) ∨ p2295 ∨ (¬ p2274) ∨ (¬ p4702) ∨ (¬ p2563))
    : (¬ p4153) ∨ (¬ p2274) ∨ (¬ p2563) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h98631 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124381 (p2220 p2241 p2459 p2727 p3083 p3146 p4420 : Prop)
    (h105707 : p4420)
    (h98669 : p3146 ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2727) ∨ (¬ p4420) ∨ (¬ p3083) ∨ p2220)
    : p2220 ∨ (¬ p3083) ∨ (¬ p2241) ∨ p3146 ∨ (¬ p2459) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4420 := h105707;
    (Or.elim h98669 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step124383 (p2528 p3146 p3156 p4355 p4702 : Prop)
    (h106079 : p4702)
    (h98673 : p3146 ∨ p3156 ∨ (¬ p4355) ∨ (¬ p4702) ∨ (¬ p2528))
    : (¬ p4355) ∨ p3156 ∨ (¬ p2528) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h98673 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124388 (p2252 p2608 p2750 p2946 p3146 p3156 p3449 p4181 p5122 : Prop)
    (h106345 : p2750)
    (h105483 : p5122)
    (h98681 : (¬ p4181) ∨ (¬ p5122) ∨ (¬ p3449) ∨ p2946 ∨ p3156 ∨ p2608 ∨ (¬ p2750) ∨ p3146 ∨ (¬ p2252))
    : (¬ p4181) ∨ p3156 ∨ p3146 ∨ p2946 ∨ p2608 ∨ (¬ p2252) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p5122 := h105483;
    (Or.elim h98681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124389 (p2254 p2608 p2829 p2946 p3146 p3156 p3483 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h98682 : (¬ p3483) ∨ p3146 ∨ (¬ p4330) ∨ (¬ p2254) ∨ p3156 ∨ (¬ p2829) ∨ p2946 ∨ (¬ p2608))
    : p2946 ∨ p3156 ∨ (¬ p2829) ∨ p3146 ∨ (¬ p3483) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h98682 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124390 (p2098 p2156 p2284 p2459 p2958 p3156 p3609 p4786 p4902 : Prop)
    (h105456 : p4902)
    (h106425 : p4786)
    (h98695 : (¬ p3156) ∨ p2284 ∨ (¬ p4902) ∨ (¬ p2459) ∨ p2098 ∨ (¬ p2958) ∨ (¬ p4786) ∨ (¬ p2156) ∨ p3609)
    : (¬ p3156) ∨ p2284 ∨ p3609 ∨ (¬ p2958) ∨ (¬ p2156) ∨ (¬ p2459) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    let u8 : p4786 := h106425;
    (Or.elim h98695 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124391 (p2122 p2248 p2396 p2774 p2946 p3146 p3156 p3873 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h98697 : p2396 ∨ p2122 ∨ (¬ p4669) ∨ (¬ p3156) ∨ (¬ p2248) ∨ p2774 ∨ (¬ p3873) ∨ (¬ p2946) ∨ (¬ p3146))
    : (¬ p3156) ∨ (¬ p3873) ∨ p2396 ∨ p2122 ∨ (¬ p2946) ∨ p2774 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4669 := h105415;
    (Or.elim h98697 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124393 (p2797 p2811 p2946 p3156 p3745 p4509 : Prop)
    (h105392 : p4509)
    (h98702 : p2797 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3745) ∨ (¬ p4509) ∨ (¬ p2811))
    : p2797 ∨ (¬ p3745) ∨ (¬ p2946) ∨ (¬ p2811) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    (Or.elim h98702 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step124394 (p2284 p2553 p3156 p3958 p4119 p4140 : Prop)
    (h105378 : p3958)
    (h98705 : p2284 ∨ (¬ p3156) ∨ p2553 ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p3958))
    : (¬ p4119) ∨ (¬ p3156) ∨ (¬ p4140) ∨ p2553 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4119 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h98705 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124395 (p2248 p2946 p3156 p3193 p3276 p3379 p3969 p5119 : Prop)
    (h105365 : p2248)
    (h98707 : (¬ p3969) ∨ p3276 ∨ (¬ p3156) ∨ p3379 ∨ (¬ p3193) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p5119))
    : (¬ p3969) ∨ p3276 ∨ p3379 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3193) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h98707 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124396 (p2248 p2946 p3093 p3156 p3319 p3461 p3969 p5119 : Prop)
    (h105365 : p2248)
    (h98712 : (¬ p3969) ∨ p3461 ∨ (¬ p2248) ∨ p3319 ∨ p3093 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p5119))
    : (¬ p2946) ∨ (¬ p3969) ∨ p3461 ∨ p3093 ∨ (¬ p3156) ∨ p3319 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h98712 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124399 (p2274 p2284 p2563 p2608 p2727 p4882 : Prop)
    (h105453 : p4882)
    (h98734 : p2608 ∨ p2284 ∨ (¬ p2563) ∨ (¬ p2274) ∨ p2727 ∨ (¬ p4882))
    : p2284 ∨ p2727 ∨ (¬ p2274) ∨ p2608 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    (Or.elim h98734 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124401 (p2156 p2373 p2563 p2608 p3399 p3519 p3527 p4376 p4399 p4902 : Prop)
    (h105456 : p4902)
    (h106320 : p4376)
    (h98741 : (¬ p2373) ∨ (¬ p2156) ∨ p3527 ∨ (¬ p4376) ∨ (¬ p4399) ∨ p2563 ∨ (¬ p3519) ∨ (¬ p2608) ∨ p3399 ∨ (¬ p4902))
    : p3399 ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2156) ∨ p3527 ∨ p2563 ∨ (¬ p2608) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    let u9 : p4376 := h106320;
    (Or.elim h98741 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step124402 (p2373 p2427 p3246 p4042 p4666 : Prop)
    (h105658 : p4666)
    (h98746 : p2427 ∨ (¬ p2373) ∨ (¬ p4042) ∨ p3246 ∨ (¬ p4666))
    : (¬ p2373) ∨ p2427 ∨ p3246 ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h98746 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124403 (p2177 p2373 p2427 p4042 p4559 : Prop)
    (h105701 : p4559)
    (h98747 : (¬ p4042) ∨ (¬ p2373) ∨ p2177 ∨ p2427 ∨ (¬ p4559))
    : (¬ p2373) ∨ p2427 ∨ (¬ p4042) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4559 := h105701;
    (Or.elim h98747 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124405 (p2264 p2373 p2427 p4042 p4280 : Prop)
    (h105599 : p4280)
    (h98760 : (¬ p4042) ∨ (¬ p2373) ∨ p2264 ∨ p2427 ∨ (¬ p4280))
    : (¬ p2373) ∨ p2427 ∨ p2264 ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    (Or.elim h98760 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124414 (p2553 p2573 p2696 p3755 p3791 p4419 p4826 p5284 : Prop)
    (h105444 : p4826)
    (h98803 : (¬ p5284) ∨ p3755 ∨ p2696 ∨ (¬ p2553) ∨ (¬ p4826) ∨ (¬ p4419) ∨ (¬ p3791) ∨ (¬ p2573))
    : (¬ p3791) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p2573) ∨ (¬ p4419) ∨ p2696 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4826 := h105444;
    (Or.elim h98803 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124416 (p2255 p2509 p2651 p3083 p3402 : Prop)
    (h105367 : p2255)
    (h48491 : (¬ p2255) ∨ (¬ p2509) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3402))
    : (¬ p2509) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h48491 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124418 (p2630 p2745 p3193 p3343 p3402 : Prop)
    (h105523 : p2745)
    (h58770 : (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402))
    : (¬ p3193) ∨ (¬ p3402) ∨ (¬ p3343) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h58770 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124419 (p2255 p2651 p3193 p3343 p3402 : Prop)
    (h105367 : p2255)
    (h48292 : (¬ p2255) ∨ (¬ p2651) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402))
    : (¬ p3193) ∨ (¬ p3402) ∨ (¬ p2651) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h48292 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124424 (p2177 p2210 p2459 p2891 p3146 p4556 : Prop)
    (h105399 : p4556)
    (h98852 : (¬ p2891) ∨ p3146 ∨ (¬ p2177) ∨ (¬ p4556) ∨ (¬ p2210) ∨ (¬ p2459))
    : p3146 ∨ (¬ p2891) ∨ (¬ p2459) ∨ (¬ p2210) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    (Or.elim h98852 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step124427 (p2264 p2881 p2891 p4386 p4960 : Prop)
    (h106209 : p4960)
    (h98858 : (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4960) ∨ p2264 ∨ (¬ p4386))
    : (¬ p4386) ∨ (¬ p2891) ∨ p2264 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h98858 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124428 (p2807 p2891 p2946 p3699 p4960 : Prop)
    (h106209 : p4960)
    (h98859 : (¬ p3699) ∨ (¬ p2946) ∨ p2807 ∨ (¬ p4960) ∨ (¬ p2891))
    : (¬ p2946) ∨ (¬ p3699) ∨ p2807 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h98859 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124430 (p2751 p2891 p2957 p3051 p3136 p4365 : Prop)
    (h106343 : p2751)
    (h98865 : (¬ p4365) ∨ (¬ p2957) ∨ (¬ p2891) ∨ p3136 ∨ (¬ p2751) ∨ p3051)
    : p3136 ∨ p3051 ∨ (¬ p4365) ∨ (¬ p2957) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h98865 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step124431 (p2427 p2850 p2891 p3948 p5217 : Prop)
    (h105493 : p5217)
    (h98874 : (¬ p3948) ∨ (¬ p2891) ∨ p2850 ∨ p2427 ∨ (¬ p5217))
    : (¬ p2891) ∨ p2850 ∨ p2427 ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    (Or.elim h98874 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124436 (p2284 p2807 p2946 p4555 : Prop)
    (h105542 : p4555)
    (h98897 : (¬ p2284) ∨ (¬ p2946) ∨ (¬ p4555) ∨ p2807)
    : p2807 ∨ (¬ p2946) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4555 := h105542;
    (Or.elim h98897 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step124438 (p2187 p2284 p2598 p2911 p2946 p3201 p4133 p4786 : Prop)
    (h105712 : p4133)
    (h106425 : p4786)
    (h98900 : (¬ p2284) ∨ p3201 ∨ p2911 ∨ (¬ p4133) ∨ (¬ p2187) ∨ p2598 ∨ (¬ p2946) ∨ (¬ p4786))
    : p3201 ∨ p2598 ∨ (¬ p2187) ∨ (¬ p2946) ∨ (¬ p2284) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4133 := h105712;
    let u7 : p4786 := h106425;
    (Or.elim h98900 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124440 (p2187 p2248 p2284 p2459 p2946 p3073 p3449 p4133 : Prop)
    (h105365 : p2248)
    (h105712 : p4133)
    (h98904 : p3073 ∨ p3449 ∨ (¬ p2459) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2248))
    : p3073 ∨ (¬ p2946) ∨ (¬ p2459) ∨ (¬ p2284) ∨ p3449 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4133 := h105712;
    (Or.elim h98904 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124441 (p2187 p2284 p2819 p4906 : Prop)
    (h105632 : p4906)
    (h98906 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4906) ∨ p2819)
    : (¬ p2284) ∨ p2819 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4906 := h105632;
    (Or.elim h98906 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step124446 (p2248 p2946 p3093 p3115 p3680 p3923 p5123 p5580 : Prop)
    (h105365 : p2248)
    (h98922 : (¬ p5580) ∨ (¬ p5123) ∨ p3093 ∨ (¬ p2248) ∨ (¬ p3923) ∨ (¬ p2946) ∨ (¬ p3680) ∨ (¬ p3115))
    : (¬ p3680) ∨ (¬ p3115) ∨ (¬ p2946) ∨ (¬ p3923) ∨ (¬ p5580) ∨ p3093 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h98922 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124455 (p2860 p3125 p3319 p4512 p4875 : Prop)
    (h106227 : p4875)
    (h98953 : (¬ p3125) ∨ p3319 ∨ (¬ p2860) ∨ (¬ p4512) ∨ (¬ p4875))
    : (¬ p4512) ∨ (¬ p2860) ∨ p3319 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4875 := h106227;
    (Or.elim h98953 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124458 (p2136 p2156 p2192 p2598 p4313 p4418 p4752 : Prop)
    (h105434 : p4752)
    (h98970 : (¬ p2192) ∨ (¬ p4418) ∨ p2156 ∨ (¬ p2598) ∨ (¬ p2136) ∨ (¬ p4313) ∨ (¬ p4752))
    : (¬ p2598) ∨ p2156 ∨ (¬ p4418) ∨ (¬ p2192) ∨ (¬ p4313) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4752 := h105434;
    (Or.elim h98970 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step124460 (p2192 p2284 p2751 p3136 p4365 : Prop)
    (h106343 : p2751)
    (h98976 : (¬ p4365) ∨ (¬ p2751) ∨ (¬ p2192) ∨ p3136 ∨ p2284)
    : p3136 ∨ (¬ p2192) ∨ (¬ p4365) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h98976 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124461 (p2136 p2156 p2192 p2598 p2742 p4365 p4752 : Prop)
    (h105434 : p4752)
    (h98978 : (¬ p4365) ∨ (¬ p2742) ∨ p2156 ∨ (¬ p2192) ∨ (¬ p2136) ∨ (¬ p4752) ∨ (¬ p2598))
    : (¬ p2136) ∨ (¬ p2598) ∨ p2156 ∨ (¬ p2742) ∨ (¬ p4365) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4752 := h105434;
    (Or.elim h98978 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step124463 (p2192 p2331 p2946 p3745 p4960 : Prop)
    (h106209 : p4960)
    (h98980 : (¬ p2946) ∨ p2331 ∨ (¬ p3745) ∨ (¬ p4960) ∨ (¬ p2192))
    : p2331 ∨ (¬ p2946) ∨ (¬ p2192) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h98980 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124468 (p2192 p2210 p2254 p2264 p2274 p2807 p2911 p4712 : Prop)
    (h105366 : p2254)
    (h105422 : p4712)
    (h98990 : (¬ p2911) ∨ (¬ p2274) ∨ (¬ p2254) ∨ p2264 ∨ (¬ p4712) ∨ p2807 ∨ (¬ p2192) ∨ (¬ p2210))
    : (¬ p2911) ∨ (¬ p2192) ∨ (¬ p2210) ∨ p2264 ∨ p2807 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4712 := h105422;
    (Or.elim h98990 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124469 (p2192 p2590 p3125 p3564 p4632 : Prop)
    (h106257 : p4632)
    (h98991 : (¬ p3125) ∨ p3564 ∨ (¬ p2590) ∨ (¬ p4632) ∨ (¬ p2192))
    : (¬ p2192) ∨ p3564 ∨ (¬ p3125) ∨ (¬ p2590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    (Or.elim h98991 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124470 (p2192 p3125 p3323 p4153 p4960 : Prop)
    (h106209 : p4960)
    (h98993 : (¬ p3125) ∨ p3323 ∨ (¬ p4960) ∨ (¬ p2192) ∨ (¬ p4153))
    : (¬ p4153) ∨ (¬ p2192) ∨ p3323 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    (Or.elim h98993 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124486 (p2373 p2459 p2598 p2850 p3073 p3449 p4733 p4902 : Prop)
    (h105430 : p4733)
    (h105456 : p4902)
    (h99033 : p3449 ∨ (¬ p2598) ∨ p3073 ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p4733) ∨ (¬ p2373) ∨ (¬ p2850))
    : (¬ p2598) ∨ (¬ p2850) ∨ p3449 ∨ p3073 ∨ (¬ p2459) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4902 := h105456;
    (Or.elim h99033 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124487 (p2156 p2459 p2619 p2860 p3073 p3449 p4521 p4902 : Prop)
    (h105456 : p4902)
    (h99035 : (¬ p2619) ∨ p2860 ∨ (¬ p4902) ∨ (¬ p2156) ∨ p3073 ∨ p3449 ∨ (¬ p4521) ∨ (¬ p2459))
    : p3073 ∨ (¬ p2619) ∨ (¬ p4521) ∨ p3449 ∨ (¬ p2156) ∨ (¬ p2459) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    (Or.elim h99035 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124488 (p2528 p3073 p3083 p3453 p4811 : Prop)
    (h105633 : p4811)
    (h99039 : p3073 ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4811) ∨ (¬ p3083))
    : (¬ p3453) ∨ (¬ p3083) ∨ (¬ p2528) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3453 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h99039 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124490 (p2248 p2373 p2440 p2459 p2651 p3073 p3449 p4902 : Prop)
    (h105365 : p2248)
    (h105456 : p4902)
    (h99052 : p3449 ∨ p3073 ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p2373) ∨ p2440 ∨ (¬ p2651) ∨ (¬ p2248))
    : p3449 ∨ p3073 ∨ p2440 ∨ (¬ p2651) ∨ (¬ p2373) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4902 := h105456;
    (Or.elim h99052 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124491 (p2132 p2363 p2870 p2881 p3073 p3093 p4371 p4503 p4733 : Prop)
    (h105430 : p4733)
    (h106530 : p4503)
    (h99053 : (¬ p2881) ∨ (¬ p2870) ∨ (¬ p4733) ∨ (¬ p4503) ∨ (¬ p2132) ∨ (¬ p4371) ∨ (¬ p2363) ∨ p3073 ∨ p3093)
    : p3073 ∨ p3093 ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p4371) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : p4503 := h106530;
    (Or.elim h99053 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step124492 (p2122 p2177 p2528 p2774 p3073 p3449 p4438 p4733 : Prop)
    (h105430 : p4733)
    (h99055 : p3073 ∨ (¬ p2774) ∨ p3449 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p4438) ∨ (¬ p2528) ∨ (¬ p4733))
    : p3073 ∨ p3449 ∨ (¬ p2528) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2177) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h99055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124493 (p2248 p2363 p2663 p3073 p3083 p3201 p3389 p3449 p3683 p4596 : Prop)
    (h105365 : p2248)
    (h99056 : p3201 ∨ p3449 ∨ (¬ p4596) ∨ (¬ p2663) ∨ (¬ p3083) ∨ (¬ p2248) ∨ p3073 ∨ (¬ p2363) ∨ (¬ p3683) ∨ (¬ p3389))
    : p3201 ∨ p3073 ∨ (¬ p4596) ∨ p3449 ∨ (¬ p2363) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3683) ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2248 := h105365;
    (Or.elim h99056 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step124495 (p2246 p2608 p2744 p2761 p3073 p3286 p3449 p3506 p3950 : Prop)
    (h106503 : p2744)
    (h99061 : (¬ p3506) ∨ p3449 ∨ (¬ p3950) ∨ (¬ p2608) ∨ p2761 ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3286) ∨ p3073)
    : (¬ p3506) ∨ (¬ p3286) ∨ p3073 ∨ (¬ p2608) ∨ p2761 ∨ p3449 ∨ (¬ p2246) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h99061 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124496 (p2210 p2630 p2696 p2753 p3073 p3343 p3449 p4332 p4877 : Prop)
    (h105451 : p4877)
    (h99062 : (¬ p3343) ∨ p3449 ∨ p3073 ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p4332))
    : p3449 ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2630) ∨ (¬ p3343) ∨ (¬ p2210) ∨ p3073 ∨ (¬ p4332) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4877 := h105451;
    (Or.elim h99062 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step124497 (p2241 p2717 p2750 p2753 p3073 p3425 p3449 p3941 p5122 : Prop)
    (h106345 : p2750)
    (h105483 : p5122)
    (h99066 : p3449 ∨ (¬ p3941) ∨ (¬ p2241) ∨ p3073 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p5122) ∨ p3425 ∨ (¬ p2717))
    : p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ p3449 ∨ p3073 ∨ (¬ p3941) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p5122 := h105483;
    (Or.elim h99066 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step124498 (p2717 p2753 p3073 p3379 p3425 p3449 p3979 p4138 p5122 : Prop)
    (h105483 : p5122)
    (h99067 : p3073 ∨ p3449 ∨ (¬ p5122) ∨ (¬ p3979) ∨ (¬ p3379) ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p4138))
    : (¬ p3979) ∨ (¬ p2717) ∨ p3449 ∨ p3073 ∨ p3425 ∨ (¬ p2753) ∨ (¬ p4138) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5122 := h105483;
    (Or.elim h99067 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124504 (p2230 p2584 p3564 p3654 p4717 : Prop)
    (h105424 : p4717)
    (h99114 : (¬ p3654) ∨ p3564 ∨ (¬ p2584) ∨ (¬ p4717) ∨ p2230)
    : (¬ p3654) ∨ (¬ p2584) ∨ p2230 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h99114 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124505 (p2248 p2264 p2459 p2493 p2807 p3379 p3564 p4604 : Prop)
    (h105365 : p2248)
    (h106293 : p4604)
    (h99116 : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4604) ∨ (¬ p2248) ∨ p2493 ∨ p3379 ∨ p3564 ∨ (¬ p2459))
    : p3379 ∨ p2493 ∨ p3564 ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4604 := h106293;
    (Or.elim h99116 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step124506 (p2459 p2493 p2881 p3051 p3379 p3564 p4521 p4604 : Prop)
    (h106293 : p4604)
    (h99117 : (¬ p3051) ∨ (¬ p2881) ∨ (¬ p2459) ∨ p3379 ∨ p2493 ∨ (¬ p4521) ∨ (¬ p4604) ∨ p3564)
    : p2493 ∨ p3564 ∨ (¬ p3051) ∨ (¬ p2459) ∨ (¬ p2881) ∨ p3379 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4604 := h106293;
    (Or.elim h99117 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124509 (p2255 p2573 p2662 p2727 p3266 p3286 p3506 p3564 p4604 : Prop)
    (h105367 : p2255)
    (h106293 : p4604)
    (h99126 : p3266 ∨ (¬ p3286) ∨ p2727 ∨ (¬ p2255) ∨ (¬ p3506) ∨ (¬ p2662) ∨ p3564 ∨ (¬ p4604) ∨ p2573)
    : (¬ p3506) ∨ (¬ p3286) ∨ p2573 ∨ p2727 ∨ p3266 ∨ p3564 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2255 := h105367;
    let u8 : p4604 := h106293;
    (Or.elim h99126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124510 (p2246 p2598 p2744 p2901 p2946 p3246 p3366 p3422 p3564 p4625 : Prop)
    (h106503 : p2744)
    (h106455 : p4625)
    (h99129 : (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3366) ∨ (¬ p2246) ∨ p3422 ∨ p3564 ∨ p2598 ∨ (¬ p3246) ∨ (¬ p2744) ∨ (¬ p4625))
    : (¬ p2901) ∨ p3422 ∨ p2598 ∨ p3564 ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4625 := h106455;
    (Or.elim h99129 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124511 (p2210 p2651 p3016 p3246 p3366 p3399 p3564 p3571 p4236 p4377 p4625 : Prop)
    (h106170 : p4377)
    (h106455 : p4625)
    (h99134 : (¬ p4236) ∨ p3564 ∨ p2210 ∨ (¬ p3246) ∨ (¬ p4625) ∨ p3016 ∨ p2651 ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3571))
    : p2210 ∨ (¬ p4236) ∨ (¬ p3246) ∨ p3016 ∨ p2651 ∨ (¬ p3571) ∨ p3564 ∨ (¬ p3399) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    let u10 : p4625 := h106455;
    (Or.elim h99134 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step124512 (p2264 p2573 p2807 p3461 p3564 p3905 p3941 p4786 p5119 : Prop)
    (h106425 : p4786)
    (h99139 : p3461 ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p3905) ∨ p2573 ∨ (¬ p2807) ∨ (¬ p2264) ∨ p3564 ∨ (¬ p4786))
    : (¬ p3941) ∨ p2573 ∨ (¬ p5119) ∨ (¬ p2264) ∨ (¬ p2807) ∨ p3564 ∨ p3461 ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    (Or.elim h99139 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124513 (p2459 p2651 p2881 p3051 p3366 p3370 p3422 p3564 p3683 p4236 p4377 p4604 : Prop)
    (h106293 : p4604)
    (h106170 : p4377)
    (h99140 : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4604) ∨ (¬ p3683) ∨ (¬ p2459) ∨ p2651 ∨ (¬ p3370) ∨ p3564 ∨ p3422 ∨ (¬ p3366))
    : (¬ p3683) ∨ p3422 ∨ (¬ p3370) ∨ (¬ p3051) ∨ (¬ p2459) ∨ p2651 ∨ (¬ p3366) ∨ p3564 ∨ (¬ p2881) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3683 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4604 := h106293;
    let u11 : p4377 := h106170;
    (Or.elim h99140 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u7 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u1 q10))) (fun r10 => (False.elim (r10 u6)))))))))))))))))))))))))

theorem step124517 (p2264 p2341 p2449 p2493 p3379 p3564 p4625 p5207 : Prop)
    (h105491 : p5207)
    (h106455 : p4625)
    (h99145 : (¬ p2341) ∨ (¬ p5207) ∨ (¬ p4625) ∨ (¬ p2449) ∨ p3564 ∨ p2493 ∨ p3379 ∨ p2264)
    : p3379 ∨ p2493 ∨ (¬ p2341) ∨ p2264 ∨ p3564 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5207 := h105491;
    let u7 : p4625 := h106455;
    (Or.elim h99145 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step124519 (p2331 p2751 p2797 p2807 p2996 : Prop)
    (h106343 : p2751)
    (h99168 : p2996 ∨ p2797 ∨ (¬ p2751) ∨ (¬ p2331) ∨ p2807)
    : p2807 ∨ p2797 ∨ p2996 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h99168 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124521 (p2449 p2528 p2598 p2737 p2807 p3361 p3641 p4669 : Prop)
    (h105415 : p4669)
    (h99170 : (¬ p3641) ∨ p2737 ∨ p2449 ∨ p2807 ∨ (¬ p2598) ∨ (¬ p4669) ∨ (¬ p3361) ∨ (¬ p2528))
    : (¬ p3641) ∨ p2737 ∨ (¬ p2528) ∨ p2807 ∨ p2449 ∨ (¬ p2598) ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h99170 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124525 (p2132 p2252 p2264 p2748 p2807 p3366 p3537 p3609 p5118 p5558 : Prop)
    (h105482 : p5118)
    (h99194 : (¬ p5558) ∨ p2132 ∨ (¬ p3366) ∨ (¬ p2252) ∨ p2264 ∨ (¬ p5118) ∨ (¬ p3609) ∨ p2807 ∨ (¬ p2748) ∨ (¬ p3537))
    : (¬ p3609) ∨ (¬ p3537) ∨ p2807 ∨ p2132 ∨ (¬ p2748) ∨ p2264 ∨ (¬ p5558) ∨ (¬ p2252) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5118 := h105482;
    (Or.elim h99194 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step124529 (p2254 p2264 p2459 p2493 p2807 p3379 p3564 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h99206 : (¬ p3564) ∨ (¬ p2493) ∨ p2807 ∨ p2459 ∨ (¬ p2254) ∨ (¬ p3379) ∨ p2264 ∨ (¬ p4330))
    : (¬ p2493) ∨ (¬ p3564) ∨ p2459 ∨ (¬ p3379) ∨ p2264 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h99206 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124531 (p2252 p2264 p2459 p2608 p2750 p2807 p3449 p4181 p5122 : Prop)
    (h106345 : p2750)
    (h105483 : p5122)
    (h99221 : (¬ p4181) ∨ p2264 ∨ p2807 ∨ p2459 ∨ p2608 ∨ (¬ p2750) ∨ (¬ p5122) ∨ (¬ p3449) ∨ (¬ p2252))
    : (¬ p4181) ∨ (¬ p2252) ∨ p2807 ∨ p2459 ∨ p2608 ∨ (¬ p3449) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p5122 := h105483;
    (Or.elim h99221 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step124532 (p2249 p2449 p2807 p3631 p4365 p4431 : Prop)
    (h106513 : p2249)
    (h99224 : (¬ p3631) ∨ p2449 ∨ (¬ p4431) ∨ p2807 ∨ (¬ p2249) ∨ (¬ p4365))
    : p2807 ∨ (¬ p4431) ∨ p2449 ∨ (¬ p4365) ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    (Or.elim h99224 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step124534 (p2132 p2264 p2807 p3105 p3680 p4789 p5123 p5558 : Prop)
    (h105646 : p4789)
    (h99241 : (¬ p5558) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p3105) ∨ (¬ p2132) ∨ p2264 ∨ p2807 ∨ (¬ p4789))
    : (¬ p3680) ∨ (¬ p3105) ∨ (¬ p2132) ∨ p2264 ∨ (¬ p5558) ∨ p2807 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    (Or.elim h99241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124535 (p2192 p2210 p2254 p2264 p2459 p2807 p3125 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h99249 : p2264 ∨ (¬ p2254) ∨ (¬ p2210) ∨ p2807 ∨ p2459 ∨ (¬ p4330) ∨ (¬ p2192) ∨ (¬ p3125))
    : (¬ p3125) ∨ (¬ p2192) ∨ p2264 ∨ (¬ p2210) ∨ p2807 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h99249 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124536 (p2210 p2248 p2352 p2651 p2881 p2891 p3016 p4133 : Prop)
    (h105365 : p2248)
    (h105712 : p4133)
    (h99262 : (¬ p3016) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2248) ∨ p2210 ∨ p2891 ∨ (¬ p4133) ∨ p2881)
    : (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p2210 ∨ p2881 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4133 := h105712;
    (Or.elim h99262 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124539 (p2528 p2881 p3246 p4420 p4443 : Prop)
    (h105707 : p4420)
    (h99269 : (¬ p3246) ∨ p2528 ∨ p2881 ∨ (¬ p4443) ∨ (¬ p4420))
    : (¬ p3246) ∨ p2881 ∨ (¬ p4443) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4420 := h105707;
    (Or.elim h99269 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124540 (p2363 p2881 p3246 p4133 p4443 : Prop)
    (h105712 : p4133)
    (h99270 : p2363 ∨ (¬ p3246) ∨ (¬ p4443) ∨ p2881 ∨ (¬ p4133))
    : (¬ p3246) ∨ p2881 ∨ (¬ p4443) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    (Or.elim h99270 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124542 (p2132 p2246 p2352 p2651 p2744 p2870 p2881 p3016 p3366 p4133 : Prop)
    (h106503 : p2744)
    (h105712 : p4133)
    (h99275 : (¬ p2352) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p4133) ∨ (¬ p2246) ∨ p2870 ∨ (¬ p2744) ∨ p2132 ∨ p2881)
    : p2870 ∨ p2132 ∨ p2881 ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4133 := h105712;
    (Or.elim h99275 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u2 r8)))))))))))))))))))))

theorem step124544 (p2264 p2553 p2598 p2807 p2881 p3422 p4556 p4786 : Prop)
    (h105399 : p4556)
    (h106425 : p4786)
    (h99283 : (¬ p2264) ∨ p2598 ∨ (¬ p4786) ∨ (¬ p2807) ∨ p2881 ∨ (¬ p4556) ∨ p2553 ∨ p3422)
    : p3422 ∨ p2598 ∨ p2881 ∨ p2553 ∨ (¬ p2264) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4556 := h105399;
    let u7 : p4786 := h106425;
    (Or.elim h99283 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step124546 (p2761 p2881 p3680 p4192 p4668 : Prop)
    (h105414 : p4668)
    (h99285 : p2761 ∨ (¬ p3680) ∨ (¬ p4668) ∨ p2881 ∨ (¬ p4192))
    : (¬ p3680) ∨ (¬ p4192) ∨ p2761 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    (Or.elim h99285 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124549 (p2255 p2493 p2651 p3016 p3402 : Prop)
    (h105367 : p2255)
    (h99300 : (¬ p2651) ∨ (¬ p2255) ∨ (¬ p3016) ∨ p2493 ∨ (¬ p3402))
    : p2493 ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h99300 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124552 (p2156 p2284 p2386 p2493 p3016 p3413 p4031 p4705 : Prop)
    (h106238 : p4705)
    (h99323 : (¬ p2284) ∨ (¬ p3016) ∨ (¬ p2386) ∨ (¬ p4705) ∨ (¬ p4031) ∨ (¬ p3413) ∨ p2156 ∨ p2493)
    : p2156 ∨ p2493 ∨ (¬ p2386) ∨ (¬ p3413) ∨ (¬ p2284) ∨ (¬ p3016) ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4705 := h106238;
    (Or.elim h99323 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124553 (p2177 p2264 p2417 p2449 p4276 : Prop)
    (h105516 : p4276)
    (h99328 : (¬ p2449) ∨ p2417 ∨ (¬ p4276) ∨ (¬ p2177) ∨ p2264)
    : p2417 ∨ (¬ p2177) ∨ p2264 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h99328 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124554 (p2177 p2264 p2630 p2881 p3005 p4280 : Prop)
    (h105599 : p4280)
    (h99341 : p3005 ∨ (¬ p4280) ∨ (¬ p2177) ∨ (¬ p2881) ∨ (¬ p2630) ∨ p2264)
    : (¬ p2630) ∨ p3005 ∨ (¬ p2881) ∨ p2264 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4280 := h105599;
    (Or.elim h99341 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step124556 (p2254 p2264 p2459 p2608 p2807 p2829 p3483 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h99355 : (¬ p3483) ∨ (¬ p2829) ∨ (¬ p2254) ∨ p2459 ∨ (¬ p2608) ∨ p2807 ∨ (¬ p4330) ∨ p2264)
    : (¬ p3483) ∨ p2459 ∨ (¬ p2608) ∨ (¬ p2829) ∨ p2264 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h99355 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124557 (p2254 p2264 p2459 p2608 p2807 p2839 p3105 p4450 : Prop)
    (h105366 : p2254)
    (h99357 : (¬ p3105) ∨ p2264 ∨ (¬ p2839) ∨ p2459 ∨ (¬ p4450) ∨ p2807 ∨ (¬ p2254) ∨ (¬ p2608))
    : (¬ p3105) ∨ p2807 ∨ (¬ p2608) ∨ p2459 ∨ (¬ p4450) ∨ (¬ p2839) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h99357 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124558 (p2254 p2264 p2406 p2459 p2807 p2982 p3379 p4450 : Prop)
    (h105366 : p2254)
    (h99359 : p2264 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2459 ∨ (¬ p4450) ∨ (¬ p2254) ∨ p2807)
    : (¬ p2406) ∨ p2807 ∨ p2264 ∨ (¬ p2982) ∨ (¬ p3379) ∨ p2459 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h99359 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124561 (p2230 p2241 p2264 p2427 p2996 p3246 p4668 p5190 : Prop)
    (h105414 : p4668)
    (h105487 : p5190)
    (h99367 : (¬ p3246) ∨ p2241 ∨ (¬ p2996) ∨ (¬ p2230) ∨ (¬ p4668) ∨ (¬ p5190) ∨ (¬ p2427) ∨ p2264)
    : p2241 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2996) ∨ p2264 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4668 := h105414;
    let u7 : p5190 := h105487;
    (Or.elim h99367 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124562 (p2210 p2264 p2685 p2696 p3366 p3399 p3631 p4377 p4668 : Prop)
    (h105414 : p4668)
    (h106170 : p4377)
    (h99372 : (¬ p3631) ∨ p2210 ∨ p2264 ∨ p2696 ∨ (¬ p3366) ∨ p2685 ∨ (¬ p3399) ∨ (¬ p4668) ∨ (¬ p4377))
    : p2696 ∨ p2685 ∨ (¬ p3631) ∨ p2264 ∨ p2210 ∨ (¬ p3399) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4668 := h105414;
    let u8 : p4377 := h106170;
    (Or.elim h99372 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124563 (p2264 p2727 p3527 p4652 : Prop)
    (h105413 : p4652)
    (h99374 : (¬ p3527) ∨ p2727 ∨ (¬ p4652) ∨ p2264)
    : (¬ p3527) ∨ p2727 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4652 := h105413;
    (Or.elim h99374 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step124564 (p2255 p2264 p2341 p2996 p4104 : Prop)
    (h105367 : p2255)
    (h99376 : (¬ p2341) ∨ (¬ p2996) ∨ (¬ p4104) ∨ p2264 ∨ (¬ p2255))
    : (¬ p2341) ∨ (¬ p2996) ∨ (¬ p4104) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h99376 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124566 (p2264 p2417 p2807 p2922 p2946 p3136 p3379 p4668 : Prop)
    (h105414 : p4668)
    (h99381 : (¬ p2946) ∨ (¬ p2417) ∨ p2264 ∨ (¬ p4668) ∨ p3136 ∨ (¬ p3379) ∨ p2807 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2417) ∨ p2807 ∨ p2264 ∨ (¬ p2946) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4668 := h105414;
    (Or.elim h99381 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124567 (p2156 p2252 p2264 p2459 p2750 p2807 p2860 p3105 p3370 p3371 p4450 : Prop)
    (h106345 : p2750)
    (h99383 : (¬ p3105) ∨ (¬ p3370) ∨ (¬ p2252) ∨ p2459 ∨ p2807 ∨ (¬ p2156) ∨ (¬ p3371) ∨ (¬ p2750) ∨ p2860 ∨ p2264 ∨ (¬ p4450))
    : (¬ p3371) ∨ p2860 ∨ (¬ p2252) ∨ (¬ p3370) ∨ p2459 ∨ (¬ p2156) ∨ p2264 ∨ (¬ p3105) ∨ p2807 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    (Or.elim h99383 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u6 q9))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step124569 (p2264 p2470 p2528 p2685 p2696 p3146 p4079 p4736 p4902 : Prop)
    (h105431 : p4736)
    (h105456 : p4902)
    (h99390 : p2685 ∨ (¬ p2470) ∨ p2696 ∨ (¬ p4079) ∨ p3146 ∨ (¬ p4902) ∨ (¬ p2528) ∨ p2264 ∨ (¬ p4736))
    : p2696 ∨ p2685 ∨ (¬ p2470) ∨ (¬ p4079) ∨ (¬ p2528) ∨ p2264 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4902 := h105456;
    (Or.elim h99390 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step124573 (p2264 p2396 p2553 p2573 p2685 p2696 p3366 p3519 p4376 p4668 : Prop)
    (h105414 : p4668)
    (h106320 : p4376)
    (h99400 : p2685 ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p4376) ∨ p2696 ∨ p2264 ∨ (¬ p4668))
    : (¬ p2573) ∨ (¬ p2553) ∨ p2696 ∨ (¬ p3519) ∨ p2685 ∨ p2264 ∨ (¬ p3366) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4668 := h105414;
    let u9 : p4376 := h106320;
    (Or.elim h99400 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step124576 (p2187 p2192 p2210 p2264 p2685 p2696 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h99405 : p2264 ∨ p2685 ∨ (¬ p2187) ∨ (¬ p2210) ∨ (¬ p2192) ∨ p2696 ∨ (¬ p4133) ∨ (¬ p4736))
    : p2685 ∨ p2696 ∨ (¬ p2210) ∨ (¬ p2187) ∨ p2264 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4133 := h105712;
    (Or.elim h99405 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124577 (p2210 p2264 p2685 p2696 p2891 p3246 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h99406 : (¬ p2891) ∨ p2696 ∨ (¬ p4668) ∨ (¬ p2210) ∨ p2264 ∨ (¬ p3246) ∨ p2685 ∨ (¬ p4736))
    : p2696 ∨ p2685 ∨ p2264 ∨ (¬ p2210) ∨ (¬ p3246) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4668 := h105414;
    (Or.elim h99406 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124578 (p2132 p2187 p2241 p2264 p2860 p2996 p4133 p4733 : Prop)
    (h105430 : p4733)
    (h105712 : p4133)
    (h99407 : (¬ p2132) ∨ (¬ p2996) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p4733) ∨ (¬ p2860) ∨ p2264 ∨ p2241)
    : p2241 ∨ (¬ p2860) ∨ p2264 ∨ (¬ p2187) ∨ (¬ p2996) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4133 := h105712;
    (Or.elim h99407 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step124579 (p2230 p2264 p2373 p2696 p2748 p2996 p3367 p3759 p4902 : Prop)
    (h105456 : p4902)
    (h99413 : (¬ p2996) ∨ (¬ p3367) ∨ (¬ p2748) ∨ (¬ p3759) ∨ p2264 ∨ p2696 ∨ (¬ p2373) ∨ (¬ p2230) ∨ (¬ p4902))
    : (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2748) ∨ (¬ p2996) ∨ p2696 ∨ p2264 ∨ (¬ p2230) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    (Or.elim h99413 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124583 (p2264 p2341 p2663 p2685 p4790 p5201 : Prop)
    (h106424 : p4790)
    (h99434 : (¬ p2341) ∨ p2264 ∨ p2685 ∨ (¬ p4790) ∨ (¬ p5201) ∨ (¬ p2663))
    : (¬ p2341) ∨ p2685 ∨ p2264 ∨ (¬ p2663) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    (Or.elim h99434 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step124584 (p2264 p2341 p2685 p4104 p4790 : Prop)
    (h106424 : p4790)
    (h99436 : (¬ p2341) ∨ p2264 ∨ (¬ p4790) ∨ (¬ p4104) ∨ p2685)
    : (¬ p2341) ∨ p2685 ∨ (¬ p4104) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h99436 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step124585 (p2246 p2264 p2341 p2685 p2751 p4104 : Prop)
    (h106343 : p2751)
    (h99437 : (¬ p2341) ∨ p2264 ∨ (¬ p2751) ∨ (¬ p4104) ∨ p2685 ∨ (¬ p2246))
    : (¬ p2341) ∨ p2685 ∨ (¬ p4104) ∨ (¬ p2246) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h99437 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u3)))))))))))))

end ElevenRUP
