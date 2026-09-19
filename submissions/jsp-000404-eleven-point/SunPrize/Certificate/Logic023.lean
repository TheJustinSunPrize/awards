import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step65213 (p2027 p2098 p2241 p2750 p2753 p3591 p3609 p3692 p3923 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h40726 : p2027 ∨ (¬ p2098) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433))
    : (¬ p2098) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40726 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65214 (p2027 p2241 p2528 p2598 p2750 p2753 p3591 p3641 p4026 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h40728 : p2027 ∨ (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p4026) ∨ (¬ p4604))
    : (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p4026) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40728 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65215 (p2027 p2132 p2241 p2750 p2753 p3105 p3680 p4366 p4442 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h40729 : p2027 ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831))
    : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40729 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65216 (p2027 p2145 p2284 p2528 p2598 p3641 p3646 p4033 p4208 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h40730 : p2027 ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4604))
    : (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40730 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65217 (p2027 p2417 p3644 p4403 p4443 p5118 p5590 : Prop)
    (h40810 : (¬ p2027))
    (h40731 : p2027 ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4403) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5590))
    : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4403) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h40731 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step65219 (p1990 p2027 p2633 p3032 p3097 p3553 p3631 p4107 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h40734 : (¬ p1990) ∨ p2027 ∨ p2633 ∨ (¬ p3032) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3631) ∨ (¬ p4107))
    : (¬ p3032) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3631) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h40734 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step65221 (p2027 p2230 p2252 p2459 p2750 p3172 p3519 p3541 p3641 p3684 p4118 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h40738 : p2027 ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4118) ∨ (¬ p4420))
    : (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4118) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h40738 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step65222 (p2027 p2230 p2241 p2750 p3324 p3519 p3541 p3591 p3641 p3684 p4319 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h40739 : p2027 ∨ (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4319) ∨ (¬ p4596))
    : (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4319) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h40739 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step65225 (p2027 p2230 p2373 p2476 p4434 : Prop)
    (h40810 : (¬ p2027))
    (h40742 : p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2476) ∨ (¬ p4434))
    : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2476) ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h40742 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step65227 (p1977 p2027 p2241 p2633 p3548 p3631 p3821 p5206 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h40744 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ p2633 ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p5206))
    : (¬ p2241) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h40744 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step65228 (p2027 p2210 p2373 p3551 p4210 p4902 p5206 : Prop)
    (h40810 : (¬ p2027))
    (h40745 : p2027 ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3551) ∨ (¬ p4210) ∨ (¬ p4902) ∨ (¬ p5206))
    : (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3551) ∨ (¬ p4210) ∨ (¬ p4902) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h40745 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step65229 (p2027 p3516 p3551 p3692 p4443 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h40746 : p2027 ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902))
    : (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h40746 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step65230 (p2027 p2252 p2504 p2750 p3093 p3414 p3888 p3947 p3954 p4381 p5250 : Prop)
    (h40810 : (¬ p2027))
    (h40747 : p2027 ∨ (¬ p2252) ∨ (¬ p2504) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4381) ∨ (¬ p5250))
    : (¬ p2252) ∨ (¬ p2504) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4381) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40747 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65231 (p2027 p2166 p2210 p2252 p2459 p2750 p3172 p3954 p4118 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h40748 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3954) ∨ (¬ p4118) ∨ (¬ p4902))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3954) ∨ (¬ p4118) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40748 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65233 (p2027 p2098 p2963 p3266 p3568 p3609 p4260 p4789 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h40750 : p2027 ∨ (¬ p2098) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p3568) ∨ (¬ p3609) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831))
    : (¬ p2098) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p3568) ∨ (¬ p3609) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40750 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65234 (p2027 p2753 p3097 p3619 p3645 p3646 p3670 p4107 p4444 p4669 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h40751 : p2027 ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3619) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4877))
    : (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3619) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40751 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65235 (p2027 p2470 p2963 p3333 p3362 p3568 p3874 p4107 p4638 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h40752 : p2027 ∨ (¬ p2470) ∨ (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3874) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4789))
    : (¬ p2470) ∨ (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3874) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40752 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65236 (p1982 p2027 p2633 p2761 p3548 p3631 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h40753 : (¬ p1982) ∨ p2027 ∨ p2633 ∨ (¬ p2761) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4444))
    : (¬ p2761) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h40753 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step65240 (p2027 p2761 p3516 p4322 p4402 p4990 : Prop)
    (h40810 : (¬ p2027))
    (h40757 : p2027 ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4990))
    : (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h40757 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step65241 (p1978 p2027 p2284 p2633 p3570 p3646 p4320 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h40758 : (¬ p1978) ∨ p2027 ∨ (¬ p2284) ∨ p2633 ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4320))
    : (¬ p2284) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h40758 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step65242 (p2027 p2145 p2284 p2459 p2717 p3471 p3646 p4208 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h40762 : p2027 ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p5059))
    : (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40762 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65243 (p2027 p3292 p3333 p3362 p3389 p3461 p3876 p4789 p5284 p5322 : Prop)
    (h40810 : (¬ p2027))
    (h40763 : p2027 ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4789) ∨ (¬ p5284) ∨ (¬ p5322))
    : (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4789) ∨ (¬ p5284) ∨ (¬ p5322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3292 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40763 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65244 (p2027 p2717 p2963 p3471 p3941 p4037 p4191 p4789 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h40764 : p2027 ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p5119))
    : (¬ p2717) ∨ (¬ p2963) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40764 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65246 (p2027 p2241 p2573 p2750 p2753 p3333 p3362 p3548 p3584 p4366 p4451 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h40766 : p2027 ∨ (¬ p2241) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3584) ∨ (¬ p4366) ∨ (¬ p4451) ∨ (¬ p4668))
    : (¬ p2241) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3584) ∨ (¬ p4366) ∨ (¬ p4451) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h40766 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step65247 (p2027 p2241 p2363 p2750 p2753 p2774 p2819 p3555 p4363 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h40767 : p2027 ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059))
    : (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40767 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65248 (p2027 p2241 p2750 p2753 p3276 p3355 p3362 p3817 p4366 p4444 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h40768 : p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669))
    : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40768 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65249 (p2027 p3707 p3923 p4025 p4191 p4501 p5153 : Prop)
    (h40810 : (¬ p2027))
    (h40769 : p2027 ∨ (¬ p3707) ∨ (¬ p3923) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4501) ∨ (¬ p5153))
    : (¬ p3707) ∨ (¬ p3923) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4501) ∨ (¬ p5153) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h40769 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step65253 (p2027 p2241 p2476 p2518 p2750 p3541 p4108 : Prop)
    (h40810 : (¬ p2027))
    (h40774 : p2027 ∨ (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108))
    : (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h40774 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step65255 (p2027 p2363 p2774 p2819 p2952 p3690 p4320 p4669 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h40776 : p2027 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) ∨ (¬ p4789))
    : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40776 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65256 (p2027 p2363 p2753 p2774 p2819 p2901 p3556 p3645 p4208 p4877 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h40777 : p2027 ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4208) ∨ (¬ p4877) ∨ (¬ p5059))
    : (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4208) ∨ (¬ p4877) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40777 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65259 (p2027 p2598 p2952 p3276 p3333 p4320 p4789 p4831 p5660 : Prop)
    (h40810 : (¬ p2027))
    (h40781 : p2027 ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4320) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4320) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40781 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65260 (p2027 p2598 p2963 p3276 p3333 p3568 p4260 p4789 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h40782 : p2027 ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831))
    : (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h40782 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step65262 (p2007 p2027 p2114 p2534 p3449 p3609 p3954 p5315 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h40787 : (¬ p2007) ∨ p2027 ∨ p2114 ∨ (¬ p2534) ∨ (¬ p3449) ∨ (¬ p3609) ∨ (¬ p3954) ∨ (¬ p5315))
    : (¬ p2534) ∨ (¬ p3449) ∨ (¬ p3609) ∨ (¬ p3954) ∨ (¬ p5315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2007 := h2167;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h40787 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step65263 (p2027 p2284 p2417 p2598 p2950 p3201 p3646 p3951 p4208 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h40788 : p2027 ∨ (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2950) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4789))
    : (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2950) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40788 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65265 (p2027 p2241 p2528 p2598 p2750 p2753 p3641 p3860 p5118 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h40790 : p2027 ∨ (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693))
    : (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40790 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65266 (p1982 p2027 p2169 p3323 p3324 p3461 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h40791 : (¬ p1982) ∨ p2027 ∨ p2169 ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3461) ∨ (¬ p4444))
    : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3461) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h40791 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step65267 (p2027 p2252 p2417 p2750 p2933 p2952 p3399 p3570 p3954 p4320 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h40792 : p2027 ∨ (¬ p2252) ∨ (¬ p2417) ∨ (¬ p2750) ∨ (¬ p2933) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4668))
    : (¬ p2252) ∨ (¬ p2417) ∨ (¬ p2750) ∨ (¬ p2933) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40792 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65269 (p1977 p2027 p2169 p2241 p3452 p3574 p3956 p4116 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h40794 : (¬ p1977) ∨ p2027 ∨ p2169 ∨ (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4116))
    : (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h40794 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step65270 (p2027 p2241 p2459 p2717 p2750 p2753 p3471 p3555 p4363 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h40799 : p2027 ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059))
    : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h40799 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step65271 (p2027 p2132 p2241 p2619 p2750 p2753 p3032 p3146 p3947 p4366 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h40800 : p2027 ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40800 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65274 (p1977 p2027 p2241 p2764 p3193 p3452 p4425 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h40803 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ p2764 ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425))
    : (¬ p2241) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h40803 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step65275 (p2027 p2241 p2363 p2750 p2753 p2774 p2819 p3032 p3947 p4366 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h40804 : p2027 ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h40804 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step65277 (p2027 p3193 p3229 p3452 p3830 : Prop)
    (h40810 : (¬ p2027))
    (h40806 : p2027 ∨ (¬ p3193) ∨ (¬ p3229) ∨ (¬ p3452) ∨ (¬ p3830))
    : (¬ p3193) ∨ (¬ p3229) ∨ (¬ p3452) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3229 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h40806 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step65290 (p1874 p1880 p4265 : Prop)
    (h6438 : (¬ p1874) ∨ p4265)
    (h6439 : (¬ p1880) ∨ p4265)
    (h2042 : p1874 ∨ p1880)
    : p4265 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4265) := (fun h => hn h);
    let u1 : (¬ p1874) := (Or.elim h6438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1880) := (Or.elim h6439 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2042 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65291 (p4265 p4266 : Prop)
    (h65290 : p4265)
    (h6456 : (¬ p4265) ∨ p4266)
    : p4266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4266) := (fun h => hn h);
    let u1 : p4265 := h65290;
    (Or.elim h6456 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65292 (p4266 p5736 : Prop)
    (h65291 : p4266)
    (h10665 : (¬ p4266) ∨ p5736)
    : p5736 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5736) := (fun h => hn h);
    let u1 : p4266 := h65291;
    (Or.elim h10665 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65293 (p5736 p6192 : Prop)
    (h65292 : p5736)
    (h16420 : (¬ p5736) ∨ p6192)
    : p6192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6192) := (fun h => hn h);
    let u1 : p5736 := h65292;
    (Or.elim h16420 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65294 (p1862 p1868 p4246 : Prop)
    (h6380 : (¬ p1862) ∨ p4246)
    (h6381 : (¬ p1868) ∨ p4246)
    (h2029 : p1862 ∨ p1868)
    : p4246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4246) := (fun h => hn h);
    let u1 : (¬ p1862) := (Or.elim h6380 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1868) := (Or.elim h6381 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2029 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65295 (p4246 p4247 : Prop)
    (h65294 : p4246)
    (h6398 : (¬ p4246) ∨ p4247)
    : p4247 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4247) := (fun h => hn h);
    let u1 : p4246 := h65294;
    (Or.elim h6398 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65296 (p4247 p5725 : Prop)
    (h65295 : p4247)
    (h10540 : (¬ p4247) ∨ p5725)
    : p5725 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5725) := (fun h => hn h);
    let u1 : p4247 := h65295;
    (Or.elim h10540 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65297 (p5725 p6189 : Prop)
    (h65296 : p5725)
    (h16045 : (¬ p5725) ∨ p6189)
    : p6189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6189) := (fun h => hn h);
    let u1 : p5725 := h65296;
    (Or.elim h16045 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65298 (p1850 p1856 p4221 : Prop)
    (h6331 : (¬ p1850) ∨ p4221)
    (h6332 : (¬ p1856) ∨ p4221)
    (h2016 : p1850 ∨ p1856)
    : p4221 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4221) := (fun h => hn h);
    let u1 : (¬ p1850) := (Or.elim h6331 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1856) := (Or.elim h6332 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2016 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65299 (p4221 p4222 : Prop)
    (h65298 : p4221)
    (h6349 : (¬ p4221) ∨ p4222)
    : p4222 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4222) := (fun h => hn h);
    let u1 : p4221 := h65298;
    (Or.elim h6349 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65300 (p4222 p5713 : Prop)
    (h65299 : p4222)
    (h10444 : (¬ p4222) ∨ p5713)
    : p5713 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5713) := (fun h => hn h);
    let u1 : p4222 := h65299;
    (Or.elim h10444 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65301 (p5713 p6186 : Prop)
    (h65300 : p5713)
    (h15780 : (¬ p5713) ∨ p6186)
    : p6186 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6186) := (fun h => hn h);
    let u1 : p5713 := h65300;
    (Or.elim h15780 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65306 (p1826 p1832 p4174 : Prop)
    (h6238 : (¬ p1826) ∨ p4174)
    (h6239 : (¬ p1832) ∨ p4174)
    (h1990 : p1826 ∨ p1832)
    : p4174 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4174) := (fun h => hn h);
    let u1 : (¬ p1826) := (Or.elim h6238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1832) := (Or.elim h6239 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1990 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65307 (p4174 p4175 : Prop)
    (h65306 : p4174)
    (h6256 : (¬ p4174) ∨ p4175)
    : p4175 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4175) := (fun h => hn h);
    let u1 : p4174 := h65306;
    (Or.elim h6256 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65308 (p4175 p5689 : Prop)
    (h65307 : p4175)
    (h10237 : (¬ p4175) ∨ p5689)
    : p5689 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5689) := (fun h => hn h);
    let u1 : p4175 := h65307;
    (Or.elim h10237 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65309 (p5689 p6180 : Prop)
    (h65308 : p5689)
    (h15275 : (¬ p5689) ∨ p6180)
    : p6180 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6180) := (fun h => hn h);
    let u1 : p5689 := h65308;
    (Or.elim h15275 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65310 (p1814 p1820 p4159 : Prop)
    (h6209 : (¬ p1814) ∨ p4159)
    (h6210 : (¬ p1820) ∨ p4159)
    (h1977 : p1814 ∨ p1820)
    : p4159 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4159) := (fun h => hn h);
    let u1 : (¬ p1814) := (Or.elim h6209 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1820) := (Or.elim h6210 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1977 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65311 (p4159 p4160 : Prop)
    (h65310 : p4159)
    (h6227 : (¬ p4159) ∨ p4160)
    : p4160 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4160) := (fun h => hn h);
    let u1 : p4159 := h65310;
    (Or.elim h6227 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65312 (p4160 p5677 : Prop)
    (h65311 : p4160)
    (h10201 : (¬ p4160) ∨ p5677)
    : p5677 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5677) := (fun h => hn h);
    let u1 : p4160 := h65311;
    (Or.elim h10201 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65313 (p5677 p6177 : Prop)
    (h65312 : p5677)
    (h15166 : (¬ p5677) ∨ p6177)
    : p6177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6177) := (fun h => hn h);
    let u1 : p5677 := h65312;
    (Or.elim h15166 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65314 (p1802 p1808 p4142 : Prop)
    (h6179 : (¬ p1802) ∨ p4142)
    (h6180 : (¬ p1808) ∨ p4142)
    (h1964 : p1802 ∨ p1808)
    : p4142 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4142) := (fun h => hn h);
    let u1 : (¬ p1802) := (Or.elim h6179 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1808) := (Or.elim h6180 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1964 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65315 (p4142 p4143 : Prop)
    (h65314 : p4142)
    (h6197 : (¬ p4142) ∨ p4143)
    : p4143 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4143) := (fun h => hn h);
    let u1 : p4142 := h65314;
    (Or.elim h6197 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65316 (p4143 p5668 : Prop)
    (h65315 : p4143)
    (h10168 : (¬ p4143) ∨ p5668)
    : p5668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5668) := (fun h => hn h);
    let u1 : p4143 := h65315;
    (Or.elim h10168 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65317 (p5668 p6174 : Prop)
    (h65316 : p5668)
    (h15095 : (¬ p5668) ∨ p6174)
    : p6174 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6174) := (fun h => hn h);
    let u1 : p5668 := h65316;
    (Or.elim h15095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65318 (p1790 p1796 p4122 : Prop)
    (h6152 : (¬ p1790) ∨ p4122)
    (h6153 : (¬ p1796) ∨ p4122)
    (h1951 : p1790 ∨ p1796)
    : p4122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4122) := (fun h => hn h);
    let u1 : (¬ p1790) := (Or.elim h6152 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1796) := (Or.elim h6153 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1951 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65319 (p4122 p4123 : Prop)
    (h65318 : p4122)
    (h6170 : (¬ p4122) ∨ p4123)
    : p4123 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4123) := (fun h => hn h);
    let u1 : p4122 := h65318;
    (Or.elim h6170 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65320 (p4123 p5658 : Prop)
    (h65319 : p4123)
    (h10132 : (¬ p4123) ∨ p5658)
    : p5658 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5658) := (fun h => hn h);
    let u1 : p4123 := h65319;
    (Or.elim h10132 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65321 (p5658 p6171 : Prop)
    (h65320 : p5658)
    (h15015 : (¬ p5658) ∨ p6171)
    : p6171 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6171) := (fun h => hn h);
    let u1 : p5658 := h65320;
    (Or.elim h15015 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65322 (p1766 p1772 p4068 : Prop)
    (h6053 : (¬ p1766) ∨ p4068)
    (h6054 : (¬ p1772) ∨ p4068)
    (h1925 : p1766 ∨ p1772)
    : p4068 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4068) := (fun h => hn h);
    let u1 : (¬ p1766) := (Or.elim h6053 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1772) := (Or.elim h6054 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1925 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65323 (p4068 p4069 : Prop)
    (h65322 : p4068)
    (h6071 : (¬ p4068) ∨ p4069)
    : p4069 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4069) := (fun h => hn h);
    let u1 : p4068 := h65322;
    (Or.elim h6071 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65324 (p4069 p5642 : Prop)
    (h65323 : p4069)
    (h10014 : (¬ p4069) ∨ p5642)
    : p5642 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5642) := (fun h => hn h);
    let u1 : p4069 := h65323;
    (Or.elim h10014 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65325 (p5642 p6168 : Prop)
    (h65324 : p5642)
    (h14764 : (¬ p5642) ∨ p6168)
    : p6168 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6168) := (fun h => hn h);
    let u1 : p5642 := h65324;
    (Or.elim h14764 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65326 (p1754 p1760 p4056 : Prop)
    (h6031 : (¬ p1754) ∨ p4056)
    (h6032 : (¬ p1760) ∨ p4056)
    (h1912 : p1754 ∨ p1760)
    : p4056 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4056) := (fun h => hn h);
    let u1 : (¬ p1754) := (Or.elim h6031 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1760) := (Or.elim h6032 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1912 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65327 (p4056 p4057 : Prop)
    (h65326 : p4056)
    (h6049 : (¬ p4056) ∨ p4057)
    : p4057 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4057) := (fun h => hn h);
    let u1 : p4056 := h65326;
    (Or.elim h6049 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65328 (p4057 p5631 : Prop)
    (h65327 : p4057)
    (h9987 : (¬ p4057) ∨ p5631)
    : p5631 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5631) := (fun h => hn h);
    let u1 : p4057 := h65327;
    (Or.elim h9987 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65329 (p5631 p6165 : Prop)
    (h65328 : p5631)
    (h14732 : (¬ p5631) ∨ p6165)
    : p6165 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6165) := (fun h => hn h);
    let u1 : p5631 := h65328;
    (Or.elim h14732 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65330 (p1742 p1748 p4046 : Prop)
    (h6011 : (¬ p1742) ∨ p4046)
    (h6012 : (¬ p1748) ∨ p4046)
    (h1899 : p1742 ∨ p1748)
    : p4046 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4046) := (fun h => hn h);
    let u1 : (¬ p1742) := (Or.elim h6011 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1748) := (Or.elim h6012 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1899 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65331 (p4046 p4047 : Prop)
    (h65330 : p4046)
    (h6029 : (¬ p4046) ∨ p4047)
    : p4047 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4047) := (fun h => hn h);
    let u1 : p4046 := h65330;
    (Or.elim h6029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65332 (p4047 p5620 : Prop)
    (h65331 : p4047)
    (h9970 : (¬ p4047) ∨ p5620)
    : p5620 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5620) := (fun h => hn h);
    let u1 : p4047 := h65331;
    (Or.elim h9970 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65333 (p5620 p6162 : Prop)
    (h65332 : p5620)
    (h14713 : (¬ p5620) ∨ p6162)
    : p6162 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6162) := (fun h => hn h);
    let u1 : p5620 := h65332;
    (Or.elim h14713 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65334 (p1730 p1736 p4012 : Prop)
    (h5968 : (¬ p1730) ∨ p4012)
    (h5969 : (¬ p1736) ∨ p4012)
    (h1886 : p1730 ∨ p1736)
    : p4012 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4012) := (fun h => hn h);
    let u1 : (¬ p1730) := (Or.elim h5968 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1736) := (Or.elim h5969 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1886 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65335 (p4012 p4013 : Prop)
    (h65334 : p4012)
    (h5986 : (¬ p4012) ∨ p4013)
    : p4013 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4013) := (fun h => hn h);
    let u1 : p4012 := h65334;
    (Or.elim h5986 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65336 (p4013 p5608 : Prop)
    (h65335 : p4013)
    (h9894 : (¬ p4013) ∨ p5608)
    : p5608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5608) := (fun h => hn h);
    let u1 : p4013 := h65335;
    (Or.elim h9894 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65338 (p1718 p1724 p4002 : Prop)
    (h5948 : (¬ p1718) ∨ p4002)
    (h5949 : (¬ p1724) ∨ p4002)
    (h1873 : p1718 ∨ p1724)
    : p4002 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4002) := (fun h => hn h);
    let u1 : (¬ p1718) := (Or.elim h5948 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1724) := (Or.elim h5949 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1873 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65339 (p4002 p4003 : Prop)
    (h65338 : p4002)
    (h5966 : (¬ p4002) ∨ p4003)
    : p4003 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4003) := (fun h => hn h);
    let u1 : p4002 := h65338;
    (Or.elim h5966 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65340 (p4003 p5596 : Prop)
    (h65339 : p4003)
    (h9877 : (¬ p4003) ∨ p5596)
    : p5596 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5596) := (fun h => hn h);
    let u1 : p4003 := h65339;
    (Or.elim h9877 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65342 (p1706 p1712 p3991 : Prop)
    (h5925 : (¬ p1706) ∨ p3991)
    (h5926 : (¬ p1712) ∨ p3991)
    (h1860 : p1706 ∨ p1712)
    : p3991 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3991) := (fun h => hn h);
    let u1 : (¬ p1706) := (Or.elim h5925 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1712) := (Or.elim h5926 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1860 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65343 (p3991 p3992 : Prop)
    (h65342 : p3991)
    (h5943 : (¬ p3991) ∨ p3992)
    : p3992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3992) := (fun h => hn h);
    let u1 : p3991 := h65342;
    (Or.elim h5943 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65344 (p3992 p5588 : Prop)
    (h65343 : p3992)
    (h9851 : (¬ p3992) ∨ p5588)
    : p5588 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5588) := (fun h => hn h);
    let u1 : p3992 := h65343;
    (Or.elim h9851 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65345 (p5588 p6153 : Prop)
    (h65344 : p5588)
    (h14487 : (¬ p5588) ∨ p6153)
    : p6153 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6153) := (fun h => hn h);
    let u1 : p5588 := h65344;
    (Or.elim h14487 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65346 (p1694 p1700 p3972 : Prop)
    (h5893 : (¬ p1694) ∨ p3972)
    (h5894 : (¬ p1700) ∨ p3972)
    (h1847 : p1694 ∨ p1700)
    : p3972 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3972) := (fun h => hn h);
    let u1 : (¬ p1694) := (Or.elim h5893 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1700) := (Or.elim h5894 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1847 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65347 (p3972 p3973 : Prop)
    (h65346 : p3972)
    (h5911 : (¬ p3972) ∨ p3973)
    : p3973 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3973) := (fun h => hn h);
    let u1 : p3972 := h65346;
    (Or.elim h5911 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65348 (p3973 p5576 : Prop)
    (h65347 : p3973)
    (h9821 : (¬ p3973) ∨ p5576)
    : p5576 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5576) := (fun h => hn h);
    let u1 : p3973 := h65347;
    (Or.elim h9821 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65349 (p5576 p6150 : Prop)
    (h65348 : p5576)
    (h14423 : (¬ p5576) ∨ p6150)
    : p6150 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6150) := (fun h => hn h);
    let u1 : p5576 := h65348;
    (Or.elim h14423 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65350 (p1682 p1688 p3962 : Prop)
    (h5873 : (¬ p1682) ∨ p3962)
    (h5874 : (¬ p1688) ∨ p3962)
    (h1834 : p1682 ∨ p1688)
    : p3962 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3962) := (fun h => hn h);
    let u1 : (¬ p1682) := (Or.elim h5873 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1688) := (Or.elim h5874 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1834 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65351 (p3962 p3963 : Prop)
    (h65350 : p3962)
    (h5891 : (¬ p3962) ∨ p3963)
    : p3963 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3963) := (fun h => hn h);
    let u1 : p3962 := h65350;
    (Or.elim h5891 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65352 (p3963 p5566 : Prop)
    (h65351 : p3963)
    (h9804 : (¬ p3963) ∨ p5566)
    : p5566 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5566) := (fun h => hn h);
    let u1 : p3963 := h65351;
    (Or.elim h9804 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65353 (p5566 p6147 : Prop)
    (h65352 : p5566)
    (h14405 : (¬ p5566) ∨ p6147)
    : p6147 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6147) := (fun h => hn h);
    let u1 : p5566 := h65352;
    (Or.elim h14405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65354 (p1670 p1676 p3934 : Prop)
    (h5835 : (¬ p1670) ∨ p3934)
    (h5836 : (¬ p1676) ∨ p3934)
    (h1821 : p1670 ∨ p1676)
    : p3934 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3934) := (fun h => hn h);
    let u1 : (¬ p1670) := (Or.elim h5835 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1676) := (Or.elim h5836 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1821 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65355 (p3934 p3935 : Prop)
    (h65354 : p3934)
    (h5853 : (¬ p3934) ∨ p3935)
    : p3935 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3935) := (fun h => hn h);
    let u1 : p3934 := h65354;
    (Or.elim h5853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65356 (p3935 p5554 : Prop)
    (h65355 : p3935)
    (h9734 : (¬ p3935) ∨ p5554)
    : p5554 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5554) := (fun h => hn h);
    let u1 : p3935 := h65355;
    (Or.elim h9734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65357 (p5554 p6144 : Prop)
    (h65356 : p5554)
    (h14279 : (¬ p5554) ∨ p6144)
    : p6144 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6144) := (fun h => hn h);
    let u1 : p5554 := h65356;
    (Or.elim h14279 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65358 (p1658 p1664 p3924 : Prop)
    (h5815 : (¬ p1658) ∨ p3924)
    (h5816 : (¬ p1664) ∨ p3924)
    (h1808 : p1658 ∨ p1664)
    : p3924 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3924) := (fun h => hn h);
    let u1 : (¬ p1658) := (Or.elim h5815 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1664) := (Or.elim h5816 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1808 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65359 (p3924 p3925 : Prop)
    (h65358 : p3924)
    (h5833 : (¬ p3924) ∨ p3925)
    : p3925 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3925) := (fun h => hn h);
    let u1 : p3924 := h65358;
    (Or.elim h5833 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65360 (p3925 p5543 : Prop)
    (h65359 : p3925)
    (h9716 : (¬ p3925) ∨ p5543)
    : p5543 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5543) := (fun h => hn h);
    let u1 : p3925 := h65359;
    (Or.elim h9716 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65362 (p1646 p1652 p3907 : Prop)
    (h5787 : (¬ p1646) ∨ p3907)
    (h5788 : (¬ p1652) ∨ p3907)
    (h1795 : p1646 ∨ p1652)
    : p3907 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3907) := (fun h => hn h);
    let u1 : (¬ p1646) := (Or.elim h5787 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1652) := (Or.elim h5788 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1795 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65363 (p3907 p3908 : Prop)
    (h65362 : p3907)
    (h5805 : (¬ p3907) ∨ p3908)
    : p3908 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3908) := (fun h => hn h);
    let u1 : p3907 := h65362;
    (Or.elim h5805 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65364 (p3908 p5532 : Prop)
    (h65363 : p3908)
    (h9674 : (¬ p3908) ∨ p5532)
    : p5532 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5532) := (fun h => hn h);
    let u1 : p3908 := h65363;
    (Or.elim h9674 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65365 (p5532 p6138 : Prop)
    (h65364 : p5532)
    (h14180 : (¬ p5532) ∨ p6138)
    : p6138 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6138) := (fun h => hn h);
    let u1 : p5532 := h65364;
    (Or.elim h14180 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65366 (p1634 p1640 p3894 : Prop)
    (h5764 : (¬ p1634) ∨ p3894)
    (h5765 : (¬ p1640) ∨ p3894)
    (h1782 : p1634 ∨ p1640)
    : p3894 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3894) := (fun h => hn h);
    let u1 : (¬ p1634) := (Or.elim h5764 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1640) := (Or.elim h5765 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1782 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65367 (p3894 p3895 : Prop)
    (h65366 : p3894)
    (h5782 : (¬ p3894) ∨ p3895)
    : p3895 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3895) := (fun h => hn h);
    let u1 : p3894 := h65366;
    (Or.elim h5782 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65368 (p3895 p5521 : Prop)
    (h65367 : p3895)
    (h9652 : (¬ p3895) ∨ p5521)
    : p5521 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5521) := (fun h => hn h);
    let u1 : p3895 := h65367;
    (Or.elim h9652 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65369 (p5521 p6135 : Prop)
    (h65368 : p5521)
    (h14145 : (¬ p5521) ∨ p6135)
    : p6135 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6135) := (fun h => hn h);
    let u1 : p5521 := h65368;
    (Or.elim h14145 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65370 (p1622 p1628 p3881 : Prop)
    (h5741 : (¬ p1622) ∨ p3881)
    (h5742 : (¬ p1628) ∨ p3881)
    (h1769 : p1622 ∨ p1628)
    : p3881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3881) := (fun h => hn h);
    let u1 : (¬ p1622) := (Or.elim h5741 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1628) := (Or.elim h5742 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1769 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65371 (p3881 p3882 : Prop)
    (h65370 : p3881)
    (h5759 : (¬ p3881) ∨ p3882)
    : p3882 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3882) := (fun h => hn h);
    let u1 : p3881 := h65370;
    (Or.elim h5759 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65372 (p3882 p5511 : Prop)
    (h65371 : p3882)
    (h9635 : (¬ p3882) ∨ p5511)
    : p5511 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5511) := (fun h => hn h);
    let u1 : p3882 := h65371;
    (Or.elim h9635 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65374 (p1610 p1616 p3861 : Prop)
    (h5708 : (¬ p1610) ∨ p3861)
    (h5709 : (¬ p1616) ∨ p3861)
    (h1756 : p1610 ∨ p1616)
    : p3861 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3861) := (fun h => hn h);
    let u1 : (¬ p1610) := (Or.elim h5708 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1616) := (Or.elim h5709 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1756 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65375 (p3861 p3862 : Prop)
    (h65374 : p3861)
    (h5726 : (¬ p3861) ∨ p3862)
    : p3862 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3862) := (fun h => hn h);
    let u1 : p3861 := h65374;
    (Or.elim h5726 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65376 (p3862 p5499 : Prop)
    (h65375 : p3862)
    (h9596 : (¬ p3862) ∨ p5499)
    : p5499 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5499) := (fun h => hn h);
    let u1 : p3862 := h65375;
    (Or.elim h9596 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65377 (p5499 p6129 : Prop)
    (h65376 : p5499)
    (h14047 : (¬ p5499) ∨ p6129)
    : p6129 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6129) := (fun h => hn h);
    let u1 : p5499 := h65376;
    (Or.elim h14047 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65378 (p1586 p1592 p3823 : Prop)
    (h5637 : (¬ p1586) ∨ p3823)
    (h5638 : (¬ p1592) ∨ p3823)
    (h1730 : p1586 ∨ p1592)
    : p3823 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3823) := (fun h => hn h);
    let u1 : (¬ p1586) := (Or.elim h5637 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1592) := (Or.elim h5638 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1730 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65379 (p3823 p3824 : Prop)
    (h65378 : p3823)
    (h5655 : (¬ p3823) ∨ p3824)
    : p3824 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3824) := (fun h => hn h);
    let u1 : p3823 := h65378;
    (Or.elim h5655 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65380 (p3824 p5484 : Prop)
    (h65379 : p3824)
    (h9546 : (¬ p3824) ∨ p5484)
    : p5484 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5484) := (fun h => hn h);
    let u1 : p3824 := h65379;
    (Or.elim h9546 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65381 (p5484 p6126 : Prop)
    (h65380 : p5484)
    (h14020 : (¬ p5484) ∨ p6126)
    : p6126 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6126) := (fun h => hn h);
    let u1 : p5484 := h65380;
    (Or.elim h14020 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65382 (p1562 p1568 p3784 : Prop)
    (h5563 : (¬ p1562) ∨ p3784)
    (h5564 : (¬ p1568) ∨ p3784)
    (h1704 : p1562 ∨ p1568)
    : p3784 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3784) := (fun h => hn h);
    let u1 : (¬ p1562) := (Or.elim h5563 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1568) := (Or.elim h5564 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1704 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65383 (p3784 p3785 : Prop)
    (h65382 : p3784)
    (h5581 : (¬ p3784) ∨ p3785)
    : p3785 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3785) := (fun h => hn h);
    let u1 : p3784 := h65382;
    (Or.elim h5581 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65384 (p3785 p5468 : Prop)
    (h65383 : p3785)
    (h9494 : (¬ p3785) ∨ p5468)
    : p5468 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5468) := (fun h => hn h);
    let u1 : p3785 := h65383;
    (Or.elim h9494 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65385 (p5468 p6123 : Prop)
    (h65384 : p5468)
    (h13971 : (¬ p5468) ∨ p6123)
    : p6123 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6123) := (fun h => hn h);
    let u1 : p5468 := h65384;
    (Or.elim h13971 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65386 (p1538 p1544 p3748 : Prop)
    (h5488 : (¬ p1538) ∨ p3748)
    (h5489 : (¬ p1544) ∨ p3748)
    (h1678 : p1538 ∨ p1544)
    : p3748 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3748) := (fun h => hn h);
    let u1 : (¬ p1538) := (Or.elim h5488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1544) := (Or.elim h5489 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1678 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65387 (p3748 p3749 : Prop)
    (h65386 : p3748)
    (h5506 : (¬ p3748) ∨ p3749)
    : p3749 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3749) := (fun h => hn h);
    let u1 : p3748 := h65386;
    (Or.elim h5506 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65388 (p3749 p5451 : Prop)
    (h65387 : p3749)
    (h9437 : (¬ p3749) ∨ p5451)
    : p5451 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5451) := (fun h => hn h);
    let u1 : p3749 := h65387;
    (Or.elim h9437 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65389 (p5451 p6120 : Prop)
    (h65388 : p5451)
    (h13928 : (¬ p5451) ∨ p6120)
    : p6120 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6120) := (fun h => hn h);
    let u1 : p5451 := h65388;
    (Or.elim h13928 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65390 (p1526 p1532 p3730 : Prop)
    (h5462 : (¬ p1526) ∨ p3730)
    (h5463 : (¬ p1532) ∨ p3730)
    (h1665 : p1526 ∨ p1532)
    : p3730 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3730) := (fun h => hn h);
    let u1 : (¬ p1526) := (Or.elim h5462 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1532) := (Or.elim h5463 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1665 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65391 (p3730 p3731 : Prop)
    (h65390 : p3730)
    (h5480 : (¬ p3730) ∨ p3731)
    : p3731 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3731) := (fun h => hn h);
    let u1 : p3730 := h65390;
    (Or.elim h5480 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65392 (p3731 p5441 : Prop)
    (h65391 : p3731)
    (h9405 : (¬ p3731) ∨ p5441)
    : p5441 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5441) := (fun h => hn h);
    let u1 : p3731 := h65391;
    (Or.elim h9405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65393 (p5441 p6117 : Prop)
    (h65392 : p5441)
    (h13896 : (¬ p5441) ∨ p6117)
    : p6117 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6117) := (fun h => hn h);
    let u1 : p5441 := h65392;
    (Or.elim h13896 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65394 (p1514 p1520 p3720 : Prop)
    (h5442 : (¬ p1514) ∨ p3720)
    (h5443 : (¬ p1520) ∨ p3720)
    (h1652 : p1514 ∨ p1520)
    : p3720 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3720) := (fun h => hn h);
    let u1 : (¬ p1514) := (Or.elim h5442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1520) := (Or.elim h5443 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1652 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65395 (p3720 p3721 : Prop)
    (h65394 : p3720)
    (h5460 : (¬ p3720) ∨ p3721)
    : p3721 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3721) := (fun h => hn h);
    let u1 : p3720 := h65394;
    (Or.elim h5460 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65396 (p3721 p5429 : Prop)
    (h65395 : p3721)
    (h9387 : (¬ p3721) ∨ p5429)
    : p5429 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5429) := (fun h => hn h);
    let u1 : p3721 := h65395;
    (Or.elim h9387 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65398 (p1502 p1508 p3710 : Prop)
    (h5422 : (¬ p1502) ∨ p3710)
    (h5423 : (¬ p1508) ∨ p3710)
    (h1639 : p1502 ∨ p1508)
    : p3710 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3710) := (fun h => hn h);
    let u1 : (¬ p1502) := (Or.elim h5422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1508) := (Or.elim h5423 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1639 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65399 (p3710 p3711 : Prop)
    (h65398 : p3710)
    (h5440 : (¬ p3710) ∨ p3711)
    : p3711 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3711) := (fun h => hn h);
    let u1 : p3710 := h65398;
    (Or.elim h5440 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65400 (p3711 p5417 : Prop)
    (h65399 : p3711)
    (h9369 : (¬ p3711) ∨ p5417)
    : p5417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5417) := (fun h => hn h);
    let u1 : p3711 := h65399;
    (Or.elim h9369 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65401 (p5417 p6111 : Prop)
    (h65400 : p5417)
    (h13862 : (¬ p5417) ∨ p6111)
    : p6111 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6111) := (fun h => hn h);
    let u1 : p5417 := h65400;
    (Or.elim h13862 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65402 (p1490 p1496 p3700 : Prop)
    (h5402 : (¬ p1490) ∨ p3700)
    (h5403 : (¬ p1496) ∨ p3700)
    (h1626 : p1490 ∨ p1496)
    : p3700 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3700) := (fun h => hn h);
    let u1 : (¬ p1490) := (Or.elim h5402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1496) := (Or.elim h5403 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1626 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65403 (p3700 p3701 : Prop)
    (h65402 : p3700)
    (h5420 : (¬ p3700) ∨ p3701)
    : p3701 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3701) := (fun h => hn h);
    let u1 : p3700 := h65402;
    (Or.elim h5420 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65404 (p3701 p5406 : Prop)
    (h65403 : p3701)
    (h9352 : (¬ p3701) ∨ p5406)
    : p5406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5406) := (fun h => hn h);
    let u1 : p3701 := h65403;
    (Or.elim h9352 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65405 (p5406 p6108 : Prop)
    (h65404 : p5406)
    (h13841 : (¬ p5406) ∨ p6108)
    : p6108 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6108) := (fun h => hn h);
    let u1 : p5406 := h65404;
    (Or.elim h13841 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65406 (p1478 p1484 p3673 : Prop)
    (h5370 : (¬ p1478) ∨ p3673)
    (h5371 : (¬ p1484) ∨ p3673)
    (h1613 : p1478 ∨ p1484)
    : p3673 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3673) := (fun h => hn h);
    let u1 : (¬ p1478) := (Or.elim h5370 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1484) := (Or.elim h5371 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1613 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65407 (p3673 p3674 : Prop)
    (h65406 : p3673)
    (h5388 : (¬ p3673) ∨ p3674)
    : p3674 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3674) := (fun h => hn h);
    let u1 : p3673 := h65406;
    (Or.elim h5388 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65408 (p3674 p5395 : Prop)
    (h65407 : p3674)
    (h9321 : (¬ p3674) ∨ p5395)
    : p5395 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5395) := (fun h => hn h);
    let u1 : p3674 := h65407;
    (Or.elim h9321 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65409 (p5395 p6105 : Prop)
    (h65408 : p5395)
    (h13797 : (¬ p5395) ∨ p6105)
    : p6105 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6105) := (fun h => hn h);
    let u1 : p5395 := h65408;
    (Or.elim h13797 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65410 (p1466 p1472 p3663 : Prop)
    (h5350 : (¬ p1466) ∨ p3663)
    (h5351 : (¬ p1472) ∨ p3663)
    (h1600 : p1466 ∨ p1472)
    : p3663 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3663) := (fun h => hn h);
    let u1 : (¬ p1466) := (Or.elim h5350 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1472) := (Or.elim h5351 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1600 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65411 (p3663 p3664 : Prop)
    (h65410 : p3663)
    (h5368 : (¬ p3663) ∨ p3664)
    : p3664 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3664) := (fun h => hn h);
    let u1 : p3663 := h65410;
    (Or.elim h5368 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65412 (p3664 p5385 : Prop)
    (h65411 : p3664)
    (h9304 : (¬ p3664) ∨ p5385)
    : p5385 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5385) := (fun h => hn h);
    let u1 : p3664 := h65411;
    (Or.elim h9304 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65413 (p5385 p6102 : Prop)
    (h65412 : p5385)
    (h13779 : (¬ p5385) ∨ p6102)
    : p6102 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6102) := (fun h => hn h);
    let u1 : p5385 := h65412;
    (Or.elim h13779 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65414 (p1454 p1460 p3647 : Prop)
    (h5324 : (¬ p1454) ∨ p3647)
    (h5325 : (¬ p1460) ∨ p3647)
    (h1587 : p1454 ∨ p1460)
    : p3647 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3647) := (fun h => hn h);
    let u1 : (¬ p1454) := (Or.elim h5324 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1460) := (Or.elim h5325 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1587 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65415 (p3647 p3648 : Prop)
    (h65414 : p3647)
    (h5342 : (¬ p3647) ∨ p3648)
    : p3648 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3648) := (fun h => hn h);
    let u1 : p3647 := h65414;
    (Or.elim h5342 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65416 (p3648 p5376 : Prop)
    (h65415 : p3648)
    (h9268 : (¬ p3648) ∨ p5376)
    : p5376 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5376) := (fun h => hn h);
    let u1 : p3648 := h65415;
    (Or.elim h9268 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65417 (p5376 p6099 : Prop)
    (h65416 : p5376)
    (h13743 : (¬ p5376) ∨ p6099)
    : p6099 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6099) := (fun h => hn h);
    let u1 : p5376 := h65416;
    (Or.elim h13743 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65418 (p1442 p1448 p3634 : Prop)
    (h5302 : (¬ p1442) ∨ p3634)
    (h5303 : (¬ p1448) ∨ p3634)
    (h1574 : p1442 ∨ p1448)
    : p3634 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3634) := (fun h => hn h);
    let u1 : (¬ p1442) := (Or.elim h5302 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1448) := (Or.elim h5303 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1574 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65419 (p3634 p3635 : Prop)
    (h65418 : p3634)
    (h5320 : (¬ p3634) ∨ p3635)
    : p3635 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3635) := (fun h => hn h);
    let u1 : p3634 := h65418;
    (Or.elim h5320 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65420 (p3635 p5366 : Prop)
    (h65419 : p3635)
    (h9248 : (¬ p3635) ∨ p5366)
    : p5366 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5366) := (fun h => hn h);
    let u1 : p3635 := h65419;
    (Or.elim h9248 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65421 (p5366 p6096 : Prop)
    (h65420 : p5366)
    (h13712 : (¬ p5366) ∨ p6096)
    : p6096 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6096) := (fun h => hn h);
    let u1 : p5366 := h65420;
    (Or.elim h13712 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65422 (p1430 p1436 p3624 : Prop)
    (h5282 : (¬ p1430) ∨ p3624)
    (h5283 : (¬ p1436) ∨ p3624)
    (h1561 : p1430 ∨ p1436)
    : p3624 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3624) := (fun h => hn h);
    let u1 : (¬ p1430) := (Or.elim h5282 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1436) := (Or.elim h5283 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1561 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65423 (p3624 p3625 : Prop)
    (h65422 : p3624)
    (h5300 : (¬ p3624) ∨ p3625)
    : p3625 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3625) := (fun h => hn h);
    let u1 : p3624 := h65422;
    (Or.elim h5300 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65424 (p3625 p5355 : Prop)
    (h65423 : p3625)
    (h9224 : (¬ p3625) ∨ p5355)
    : p5355 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5355) := (fun h => hn h);
    let u1 : p3625 := h65423;
    (Or.elim h9224 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65425 (p5355 p6093 : Prop)
    (h65424 : p5355)
    (h13682 : (¬ p5355) ∨ p6093)
    : p6093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6093) := (fun h => hn h);
    let u1 : p5355 := h65424;
    (Or.elim h13682 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65426 (p1418 p1424 p3612 : Prop)
    (h5258 : (¬ p1418) ∨ p3612)
    (h5259 : (¬ p1424) ∨ p3612)
    (h1548 : p1418 ∨ p1424)
    : p3612 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3612) := (fun h => hn h);
    let u1 : (¬ p1418) := (Or.elim h5258 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1424) := (Or.elim h5259 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1548 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65427 (p3612 p3613 : Prop)
    (h65426 : p3612)
    (h5276 : (¬ p3612) ∨ p3613)
    : p3613 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3613) := (fun h => hn h);
    let u1 : p3612 := h65426;
    (Or.elim h5276 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65428 (p3613 p5347 : Prop)
    (h65427 : p3613)
    (h9205 : (¬ p3613) ∨ p5347)
    : p5347 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5347) := (fun h => hn h);
    let u1 : p3613 := h65427;
    (Or.elim h9205 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65430 (p1406 p1412 p3602 : Prop)
    (h5238 : (¬ p1406) ∨ p3602)
    (h5239 : (¬ p1412) ∨ p3602)
    (h1535 : p1406 ∨ p1412)
    : p3602 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3602) := (fun h => hn h);
    let u1 : (¬ p1406) := (Or.elim h5238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1412) := (Or.elim h5239 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1535 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65431 (p3602 p3603 : Prop)
    (h65430 : p3602)
    (h5256 : (¬ p3602) ∨ p3603)
    : p3603 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3603) := (fun h => hn h);
    let u1 : p3602 := h65430;
    (Or.elim h5256 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65432 (p3603 p5336 : Prop)
    (h65431 : p3603)
    (h9188 : (¬ p3603) ∨ p5336)
    : p5336 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5336) := (fun h => hn h);
    let u1 : p3603 := h65431;
    (Or.elim h9188 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65433 (p5336 p6087 : Prop)
    (h65432 : p5336)
    (h13647 : (¬ p5336) ∨ p6087)
    : p6087 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6087) := (fun h => hn h);
    let u1 : p5336 := h65432;
    (Or.elim h13647 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65434 (p1394 p1400 p3592 : Prop)
    (h5218 : (¬ p1394) ∨ p3592)
    (h5219 : (¬ p1400) ∨ p3592)
    (h1522 : p1394 ∨ p1400)
    : p3592 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3592) := (fun h => hn h);
    let u1 : (¬ p1394) := (Or.elim h5218 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1400) := (Or.elim h5219 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1522 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65435 (p3592 p3593 : Prop)
    (h65434 : p3592)
    (h5236 : (¬ p3592) ∨ p3593)
    : p3593 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3593) := (fun h => hn h);
    let u1 : p3592 := h65434;
    (Or.elim h5236 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65436 (p3593 p5326 : Prop)
    (h65435 : p3593)
    (h9171 : (¬ p3593) ∨ p5326)
    : p5326 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5326) := (fun h => hn h);
    let u1 : p3593 := h65435;
    (Or.elim h9171 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65437 (p5326 p6084 : Prop)
    (h65436 : p5326)
    (h13630 : (¬ p5326) ∨ p6084)
    : p6084 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6084) := (fun h => hn h);
    let u1 : p5326 := h65436;
    (Or.elim h13630 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65438 (p1382 p1388 p3557 : Prop)
    (h5175 : (¬ p1382) ∨ p3557)
    (h5176 : (¬ p1388) ∨ p3557)
    (h1509 : p1382 ∨ p1388)
    : p3557 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3557) := (fun h => hn h);
    let u1 : (¬ p1382) := (Or.elim h5175 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1388) := (Or.elim h5176 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1509 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65439 (p3557 p3558 : Prop)
    (h65438 : p3557)
    (h5193 : (¬ p3557) ∨ p3558)
    : p3558 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3558) := (fun h => hn h);
    let u1 : p3557 := h65438;
    (Or.elim h5193 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65440 (p3558 p5319 : Prop)
    (h65439 : p3558)
    (h9115 : (¬ p3558) ∨ p5319)
    : p5319 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5319) := (fun h => hn h);
    let u1 : p3558 := h65439;
    (Or.elim h9115 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65441 (p5319 p6081 : Prop)
    (h65440 : p5319)
    (h13558 : (¬ p5319) ∨ p6081)
    : p6081 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6081) := (fun h => hn h);
    let u1 : p5319 := h65440;
    (Or.elim h13558 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65442 (p1370 p1376 p3530 : Prop)
    (h5142 : (¬ p1370) ∨ p3530)
    (h5143 : (¬ p1376) ∨ p3530)
    (h1496 : p1370 ∨ p1376)
    : p3530 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3530) := (fun h => hn h);
    let u1 : (¬ p1370) := (Or.elim h5142 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1376) := (Or.elim h5143 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1496 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65443 (p3530 p3531 : Prop)
    (h65442 : p3530)
    (h5160 : (¬ p3530) ∨ p3531)
    : p3531 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3531) := (fun h => hn h);
    let u1 : p3530 := h65442;
    (Or.elim h5160 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65444 (p3531 p5310 : Prop)
    (h65443 : p3531)
    (h9074 : (¬ p3531) ∨ p5310)
    : p5310 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5310) := (fun h => hn h);
    let u1 : p3531 := h65443;
    (Or.elim h9074 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65445 (p5310 p6078 : Prop)
    (h65444 : p5310)
    (h13518 : (¬ p5310) ∨ p6078)
    : p6078 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6078) := (fun h => hn h);
    let u1 : p5310 := h65444;
    (Or.elim h13518 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65446 (p1358 p1364 p3520 : Prop)
    (h5122 : (¬ p1358) ∨ p3520)
    (h5123 : (¬ p1364) ∨ p3520)
    (h1483 : p1358 ∨ p1364)
    : p3520 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3520) := (fun h => hn h);
    let u1 : (¬ p1358) := (Or.elim h5122 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1364) := (Or.elim h5123 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1483 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65447 (p3520 p3521 : Prop)
    (h65446 : p3520)
    (h5140 : (¬ p3520) ∨ p3521)
    : p3521 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3521) := (fun h => hn h);
    let u1 : p3520 := h65446;
    (Or.elim h5140 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65448 (p3521 p5303 : Prop)
    (h65447 : p3521)
    (h9051 : (¬ p3521) ∨ p5303)
    : p5303 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5303) := (fun h => hn h);
    let u1 : p3521 := h65447;
    (Or.elim h9051 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65449 (p5303 p6075 : Prop)
    (h65448 : p5303)
    (h13499 : (¬ p5303) ∨ p6075)
    : p6075 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6075) := (fun h => hn h);
    let u1 : p5303 := h65448;
    (Or.elim h13499 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65450 (p1346 p1352 p3509 : Prop)
    (h5101 : (¬ p1346) ∨ p3509)
    (h5102 : (¬ p1352) ∨ p3509)
    (h1470 : p1346 ∨ p1352)
    : p3509 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3509) := (fun h => hn h);
    let u1 : (¬ p1346) := (Or.elim h5101 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1352) := (Or.elim h5102 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1470 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65451 (p3509 p3510 : Prop)
    (h65450 : p3509)
    (h5119 : (¬ p3509) ∨ p3510)
    : p3510 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3510) := (fun h => hn h);
    let u1 : p3509 := h65450;
    (Or.elim h5119 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65452 (p3510 p5292 : Prop)
    (h65451 : p3510)
    (h9032 : (¬ p3510) ∨ p5292)
    : p5292 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5292) := (fun h => hn h);
    let u1 : p3510 := h65451;
    (Or.elim h9032 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65453 (p5292 p6072 : Prop)
    (h65452 : p5292)
    (h13481 : (¬ p5292) ∨ p6072)
    : p6072 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6072) := (fun h => hn h);
    let u1 : p5292 := h65452;
    (Or.elim h13481 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65454 (p1334 p1340 p3499 : Prop)
    (h5081 : (¬ p1334) ∨ p3499)
    (h5082 : (¬ p1340) ∨ p3499)
    (h1457 : p1334 ∨ p1340)
    : p3499 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3499) := (fun h => hn h);
    let u1 : (¬ p1334) := (Or.elim h5081 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1340) := (Or.elim h5082 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1457 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65455 (p3499 p3500 : Prop)
    (h65454 : p3499)
    (h5099 : (¬ p3499) ∨ p3500)
    : p3500 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3500) := (fun h => hn h);
    let u1 : p3499 := h65454;
    (Or.elim h5099 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65456 (p3500 p5280 : Prop)
    (h65455 : p3500)
    (h9015 : (¬ p3500) ∨ p5280)
    : p5280 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5280) := (fun h => hn h);
    let u1 : p3500 := h65455;
    (Or.elim h9015 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65457 (p5280 p6069 : Prop)
    (h65456 : p5280)
    (h13463 : (¬ p5280) ∨ p6069)
    : p6069 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6069) := (fun h => hn h);
    let u1 : p5280 := h65456;
    (Or.elim h13463 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65458 (p1322 p1328 p3488 : Prop)
    (h5057 : (¬ p1322) ∨ p3488)
    (h5058 : (¬ p1328) ∨ p3488)
    (h1444 : p1322 ∨ p1328)
    : p3488 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3488) := (fun h => hn h);
    let u1 : (¬ p1322) := (Or.elim h5057 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1328) := (Or.elim h5058 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1444 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65459 (p3488 p3489 : Prop)
    (h65458 : p3488)
    (h5075 : (¬ p3488) ∨ p3489)
    : p3489 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3489) := (fun h => hn h);
    let u1 : p3488 := h65458;
    (Or.elim h5075 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65460 (p3489 p5272 : Prop)
    (h65459 : p3489)
    (h8994 : (¬ p3489) ∨ p5272)
    : p5272 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5272) := (fun h => hn h);
    let u1 : p3489 := h65459;
    (Or.elim h8994 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65461 (p5272 p6066 : Prop)
    (h65460 : p5272)
    (h13438 : (¬ p5272) ∨ p6066)
    : p6066 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6066) := (fun h => hn h);
    let u1 : p5272 := h65460;
    (Or.elim h13438 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65462 (p1310 p1316 p3476 : Prop)
    (h5035 : (¬ p1310) ∨ p3476)
    (h5036 : (¬ p1316) ∨ p3476)
    (h1431 : p1310 ∨ p1316)
    : p3476 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3476) := (fun h => hn h);
    let u1 : (¬ p1310) := (Or.elim h5035 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1316) := (Or.elim h5036 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1431 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65463 (p3476 p3477 : Prop)
    (h65462 : p3476)
    (h5053 : (¬ p3476) ∨ p3477)
    : p3477 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3477) := (fun h => hn h);
    let u1 : p3476 := h65462;
    (Or.elim h5053 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65464 (p3477 p5262 : Prop)
    (h65463 : p3477)
    (h8975 : (¬ p3477) ∨ p5262)
    : p5262 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5262) := (fun h => hn h);
    let u1 : p3477 := h65463;
    (Or.elim h8975 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65465 (p5262 p6063 : Prop)
    (h65464 : p5262)
    (h13408 : (¬ p5262) ∨ p6063)
    : p6063 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6063) := (fun h => hn h);
    let u1 : p5262 := h65464;
    (Or.elim h13408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65466 (p1298 p1304 p3464 : Prop)
    (h5010 : (¬ p1298) ∨ p3464)
    (h5011 : (¬ p1304) ∨ p3464)
    (h1418 : p1298 ∨ p1304)
    : p3464 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3464) := (fun h => hn h);
    let u1 : (¬ p1298) := (Or.elim h5010 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1304) := (Or.elim h5011 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1418 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65467 (p3464 p3465 : Prop)
    (h65466 : p3464)
    (h5028 : (¬ p3464) ∨ p3465)
    : p3465 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3465) := (fun h => hn h);
    let u1 : p3464 := h65466;
    (Or.elim h5028 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65468 (p3465 p5255 : Prop)
    (h65467 : p3465)
    (h8958 : (¬ p3465) ∨ p5255)
    : p5255 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5255) := (fun h => hn h);
    let u1 : p3465 := h65467;
    (Or.elim h8958 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65469 (p5255 p6060 : Prop)
    (h65468 : p5255)
    (h13388 : (¬ p5255) ∨ p6060)
    : p6060 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6060) := (fun h => hn h);
    let u1 : p5255 := h65468;
    (Or.elim h13388 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65470 (p1286 p1292 p3454 : Prop)
    (h4990 : (¬ p1286) ∨ p3454)
    (h4991 : (¬ p1292) ∨ p3454)
    (h1405 : p1286 ∨ p1292)
    : p3454 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3454) := (fun h => hn h);
    let u1 : (¬ p1286) := (Or.elim h4990 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1292) := (Or.elim h4991 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1405 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65471 (p3454 p3455 : Prop)
    (h65470 : p3454)
    (h5008 : (¬ p3454) ∨ p3455)
    : p3455 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3455) := (fun h => hn h);
    let u1 : p3454 := h65470;
    (Or.elim h5008 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65472 (p3455 p5245 : Prop)
    (h65471 : p3455)
    (h8941 : (¬ p3455) ∨ p5245)
    : p5245 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5245) := (fun h => hn h);
    let u1 : p3455 := h65471;
    (Or.elim h8941 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65473 (p5245 p6057 : Prop)
    (h65472 : p5245)
    (h13368 : (¬ p5245) ∨ p6057)
    : p6057 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6057) := (fun h => hn h);
    let u1 : p5245 := h65472;
    (Or.elim h13368 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65474 (p1274 p1280 p3442 : Prop)
    (h4969 : (¬ p1274) ∨ p3442)
    (h4970 : (¬ p1280) ∨ p3442)
    (h1392 : p1274 ∨ p1280)
    : p3442 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3442) := (fun h => hn h);
    let u1 : (¬ p1274) := (Or.elim h4969 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1280) := (Or.elim h4970 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1392 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65475 (p3442 p3443 : Prop)
    (h65474 : p3442)
    (h4987 : (¬ p3442) ∨ p3443)
    : p3443 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3443) := (fun h => hn h);
    let u1 : p3442 := h65474;
    (Or.elim h4987 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65476 (p3443 p5237 : Prop)
    (h65475 : p3443)
    (h8924 : (¬ p3443) ∨ p5237)
    : p5237 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5237) := (fun h => hn h);
    let u1 : p3443 := h65475;
    (Or.elim h8924 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65477 (p5237 p6054 : Prop)
    (h65476 : p5237)
    (h13347 : (¬ p5237) ∨ p6054)
    : p6054 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6054) := (fun h => hn h);
    let u1 : p5237 := h65476;
    (Or.elim h13347 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65478 (p1262 p1268 p3427 : Prop)
    (h4944 : (¬ p1262) ∨ p3427)
    (h4945 : (¬ p1268) ∨ p3427)
    (h1379 : p1262 ∨ p1268)
    : p3427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3427) := (fun h => hn h);
    let u1 : (¬ p1262) := (Or.elim h4944 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1268) := (Or.elim h4945 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1379 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65479 (p3427 p3428 : Prop)
    (h65478 : p3427)
    (h4962 : (¬ p3427) ∨ p3428)
    : p3428 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3428) := (fun h => hn h);
    let u1 : p3427 := h65478;
    (Or.elim h4962 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65480 (p3428 p5226 : Prop)
    (h65479 : p3428)
    (h8906 : (¬ p3428) ∨ p5226)
    : p5226 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5226) := (fun h => hn h);
    let u1 : p3428 := h65479;
    (Or.elim h8906 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65481 (p5226 p6051 : Prop)
    (h65480 : p5226)
    (h13325 : (¬ p5226) ∨ p6051)
    : p6051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6051) := (fun h => hn h);
    let u1 : p5226 := h65480;
    (Or.elim h13325 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65482 (p1250 p1256 p3415 : Prop)
    (h4922 : (¬ p1250) ∨ p3415)
    (h4923 : (¬ p1256) ∨ p3415)
    (h1366 : p1250 ∨ p1256)
    : p3415 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3415) := (fun h => hn h);
    let u1 : (¬ p1250) := (Or.elim h4922 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1256) := (Or.elim h4923 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1366 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65483 (p3415 p3416 : Prop)
    (h65482 : p3415)
    (h4940 : (¬ p3415) ∨ p3416)
    : p3416 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3416) := (fun h => hn h);
    let u1 : p3415 := h65482;
    (Or.elim h4940 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65484 (p3416 p5218 : Prop)
    (h65483 : p3416)
    (h8886 : (¬ p3416) ∨ p5218)
    : p5218 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5218) := (fun h => hn h);
    let u1 : p3416 := h65483;
    (Or.elim h8886 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65485 (p5218 p6048 : Prop)
    (h65484 : p5218)
    (h13305 : (¬ p5218) ∨ p6048)
    : p6048 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6048) := (fun h => hn h);
    let u1 : p5218 := h65484;
    (Or.elim h13305 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65486 (p1238 p1244 p3403 : Prop)
    (h4900 : (¬ p1238) ∨ p3403)
    (h4901 : (¬ p1244) ∨ p3403)
    (h1353 : p1238 ∨ p1244)
    : p3403 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3403) := (fun h => hn h);
    let u1 : (¬ p1238) := (Or.elim h4900 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1244) := (Or.elim h4901 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1353 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65487 (p3403 p3404 : Prop)
    (h65486 : p3403)
    (h4918 : (¬ p3403) ∨ p3404)
    : p3404 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3404) := (fun h => hn h);
    let u1 : p3403 := h65486;
    (Or.elim h4918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65488 (p3404 p5212 : Prop)
    (h65487 : p3404)
    (h8866 : (¬ p3404) ∨ p5212)
    : p5212 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5212) := (fun h => hn h);
    let u1 : p3404 := h65487;
    (Or.elim h8866 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65489 (p5212 p6045 : Prop)
    (h65488 : p5212)
    (h13287 : (¬ p5212) ∨ p6045)
    : p6045 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6045) := (fun h => hn h);
    let u1 : p5212 := h65488;
    (Or.elim h13287 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65490 (p1226 p1232 p3392 : Prop)
    (h4879 : (¬ p1226) ∨ p3392)
    (h4880 : (¬ p1232) ∨ p3392)
    (h1340 : p1226 ∨ p1232)
    : p3392 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3392) := (fun h => hn h);
    let u1 : (¬ p1226) := (Or.elim h4879 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1232) := (Or.elim h4880 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1340 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65491 (p3392 p3393 : Prop)
    (h65490 : p3392)
    (h4897 : (¬ p3392) ∨ p3393)
    : p3393 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3393) := (fun h => hn h);
    let u1 : p3392 := h65490;
    (Or.elim h4897 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65492 (p3393 p5204 : Prop)
    (h65491 : p3393)
    (h8846 : (¬ p3393) ∨ p5204)
    : p5204 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5204) := (fun h => hn h);
    let u1 : p3393 := h65491;
    (Or.elim h8846 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65493 (p5204 p6042 : Prop)
    (h65492 : p5204)
    (h13268 : (¬ p5204) ∨ p6042)
    : p6042 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6042) := (fun h => hn h);
    let u1 : p5204 := h65492;
    (Or.elim h13268 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65494 (p1214 p1220 p3382 : Prop)
    (h4859 : (¬ p1214) ∨ p3382)
    (h4860 : (¬ p1220) ∨ p3382)
    (h1327 : p1214 ∨ p1220)
    : p3382 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3382) := (fun h => hn h);
    let u1 : (¬ p1214) := (Or.elim h4859 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1220) := (Or.elim h4860 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1327 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65495 (p3382 p3383 : Prop)
    (h65494 : p3382)
    (h4877 : (¬ p3382) ∨ p3383)
    : p3383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3383) := (fun h => hn h);
    let u1 : p3382 := h65494;
    (Or.elim h4877 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65496 (p3383 p5195 : Prop)
    (h65495 : p3383)
    (h8829 : (¬ p3383) ∨ p5195)
    : p5195 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5195) := (fun h => hn h);
    let u1 : p3383 := h65495;
    (Or.elim h8829 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65497 (p5195 p6039 : Prop)
    (h65496 : p5195)
    (h13251 : (¬ p5195) ∨ p6039)
    : p6039 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6039) := (fun h => hn h);
    let u1 : p5195 := h65496;
    (Or.elim h13251 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65498 (p1202 p1208 p3372 : Prop)
    (h4839 : (¬ p1202) ∨ p3372)
    (h4840 : (¬ p1208) ∨ p3372)
    (h1314 : p1202 ∨ p1208)
    : p3372 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3372) := (fun h => hn h);
    let u1 : (¬ p1202) := (Or.elim h4839 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1208) := (Or.elim h4840 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1314 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65499 (p3372 p3373 : Prop)
    (h65498 : p3372)
    (h4857 : (¬ p3372) ∨ p3373)
    : p3373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3373) := (fun h => hn h);
    let u1 : p3372 := h65498;
    (Or.elim h4857 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65500 (p3373 p5188 : Prop)
    (h65499 : p3373)
    (h8812 : (¬ p3373) ∨ p5188)
    : p5188 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5188) := (fun h => hn h);
    let u1 : p3373 := h65499;
    (Or.elim h8812 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65501 (p5188 p6036 : Prop)
    (h65500 : p5188)
    (h13233 : (¬ p5188) ∨ p6036)
    : p6036 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6036) := (fun h => hn h);
    let u1 : p5188 := h65500;
    (Or.elim h13233 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65502 (p1190 p1196 p3348 : Prop)
    (h4810 : (¬ p1190) ∨ p3348)
    (h4811 : (¬ p1196) ∨ p3348)
    (h1301 : p1190 ∨ p1196)
    : p3348 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3348) := (fun h => hn h);
    let u1 : (¬ p1190) := (Or.elim h4810 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1196) := (Or.elim h4811 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1301 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65503 (p3348 p3349 : Prop)
    (h65502 : p3348)
    (h4828 : (¬ p3348) ∨ p3349)
    : p3349 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3349) := (fun h => hn h);
    let u1 : p3348 := h65502;
    (Or.elim h4828 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65504 (p3349 p5179 : Prop)
    (h65503 : p3349)
    (h8789 : (¬ p3349) ∨ p5179)
    : p5179 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5179) := (fun h => hn h);
    let u1 : p3349 := h65503;
    (Or.elim h8789 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65505 (p5179 p6033 : Prop)
    (h65504 : p5179)
    (h13211 : (¬ p5179) ∨ p6033)
    : p6033 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6033) := (fun h => hn h);
    let u1 : p5179 := h65504;
    (Or.elim h13211 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65506 (p1178 p1184 p3336 : Prop)
    (h4789 : (¬ p1178) ∨ p3336)
    (h4790 : (¬ p1184) ∨ p3336)
    (h1288 : p1178 ∨ p1184)
    : p3336 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3336) := (fun h => hn h);
    let u1 : (¬ p1178) := (Or.elim h4789 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1184) := (Or.elim h4790 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1288 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65507 (p3336 p3337 : Prop)
    (h65506 : p3336)
    (h4807 : (¬ p3336) ∨ p3337)
    : p3337 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3337) := (fun h => hn h);
    let u1 : p3336 := h65506;
    (Or.elim h4807 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65508 (p3337 p5168 : Prop)
    (h65507 : p3337)
    (h8772 : (¬ p3337) ∨ p5168)
    : p5168 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5168) := (fun h => hn h);
    let u1 : p3337 := h65507;
    (Or.elim h8772 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65509 (p5168 p6030 : Prop)
    (h65508 : p5168)
    (h13194 : (¬ p5168) ∨ p6030)
    : p6030 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6030) := (fun h => hn h);
    let u1 : p5168 := h65508;
    (Or.elim h13194 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65510 (p1166 p1172 p3326 : Prop)
    (h4769 : (¬ p1166) ∨ p3326)
    (h4770 : (¬ p1172) ∨ p3326)
    (h1275 : p1166 ∨ p1172)
    : p3326 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3326) := (fun h => hn h);
    let u1 : (¬ p1166) := (Or.elim h4769 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1172) := (Or.elim h4770 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1275 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65511 (p3326 p3327 : Prop)
    (h65510 : p3326)
    (h4787 : (¬ p3326) ∨ p3327)
    : p3327 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3327) := (fun h => hn h);
    let u1 : p3326 := h65510;
    (Or.elim h4787 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65512 (p3327 p5156 : Prop)
    (h65511 : p3327)
    (h8754 : (¬ p3327) ∨ p5156)
    : p5156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5156) := (fun h => hn h);
    let u1 : p3327 := h65511;
    (Or.elim h8754 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65513 (p5156 p6027 : Prop)
    (h65512 : p5156)
    (h13177 : (¬ p5156) ∨ p6027)
    : p6027 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6027) := (fun h => hn h);
    let u1 : p5156 := h65512;
    (Or.elim h13177 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65514 (p1154 p1160 p3312 : Prop)
    (h4747 : (¬ p1154) ∨ p3312)
    (h4748 : (¬ p1160) ∨ p3312)
    (h1262 : p1154 ∨ p1160)
    : p3312 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3312) := (fun h => hn h);
    let u1 : (¬ p1154) := (Or.elim h4747 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1160) := (Or.elim h4748 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1262 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65515 (p3312 p3313 : Prop)
    (h65514 : p3312)
    (h4765 : (¬ p3312) ∨ p3313)
    : p3313 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3313) := (fun h => hn h);
    let u1 : p3312 := h65514;
    (Or.elim h4765 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65516 (p3313 p5146 : Prop)
    (h65515 : p3313)
    (h8736 : (¬ p3313) ∨ p5146)
    : p5146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5146) := (fun h => hn h);
    let u1 : p3313 := h65515;
    (Or.elim h8736 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65517 (p5146 p6024 : Prop)
    (h65516 : p5146)
    (h13159 : (¬ p5146) ∨ p6024)
    : p6024 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6024) := (fun h => hn h);
    let u1 : p5146 := h65516;
    (Or.elim h13159 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65518 (p1142 p1148 p3302 : Prop)
    (h4727 : (¬ p1142) ∨ p3302)
    (h4728 : (¬ p1148) ∨ p3302)
    (h1249 : p1142 ∨ p1148)
    : p3302 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3302) := (fun h => hn h);
    let u1 : (¬ p1142) := (Or.elim h4727 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1148) := (Or.elim h4728 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1249 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65519 (p3302 p3303 : Prop)
    (h65518 : p3302)
    (h4745 : (¬ p3302) ∨ p3303)
    : p3303 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3303) := (fun h => hn h);
    let u1 : p3302 := h65518;
    (Or.elim h4745 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65520 (p3303 p5139 : Prop)
    (h65519 : p3303)
    (h8718 : (¬ p3303) ∨ p5139)
    : p5139 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5139) := (fun h => hn h);
    let u1 : p3303 := h65519;
    (Or.elim h8718 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65521 (p5139 p6021 : Prop)
    (h65520 : p5139)
    (h13142 : (¬ p5139) ∨ p6021)
    : p6021 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6021) := (fun h => hn h);
    let u1 : p5139 := h65520;
    (Or.elim h13142 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65522 (p1118 p1124 p3269 : Prop)
    (h4659 : (¬ p1118) ∨ p3269)
    (h4660 : (¬ p1124) ∨ p3269)
    (h1223 : p1118 ∨ p1124)
    : p3269 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3269) := (fun h => hn h);
    let u1 : (¬ p1118) := (Or.elim h4659 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1124) := (Or.elim h4660 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1223 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65523 (p3269 p3270 : Prop)
    (h65522 : p3269)
    (h4677 : (¬ p3269) ∨ p3270)
    : p3270 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3270) := (fun h => hn h);
    let u1 : p3269 := h65522;
    (Or.elim h4677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65524 (p3270 p5124 : Prop)
    (h65523 : p3270)
    (h8677 : (¬ p3270) ∨ p5124)
    : p5124 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5124) := (fun h => hn h);
    let u1 : p3270 := h65523;
    (Or.elim h8677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65525 (p5124 p6018 : Prop)
    (h65524 : p5124)
    (h13123 : (¬ p5124) ∨ p6018)
    : p6018 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6018) := (fun h => hn h);
    let u1 : p5124 := h65524;
    (Or.elim h13123 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65526 (p1106 p1112 p3259 : Prop)
    (h4639 : (¬ p1106) ∨ p3259)
    (h4640 : (¬ p1112) ∨ p3259)
    (h1210 : p1106 ∨ p1112)
    : p3259 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3259) := (fun h => hn h);
    let u1 : (¬ p1106) := (Or.elim h4639 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1112) := (Or.elim h4640 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1210 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65527 (p3259 p3260 : Prop)
    (h65526 : p3259)
    (h4657 : (¬ p3259) ∨ p3260)
    : p3260 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3260) := (fun h => hn h);
    let u1 : p3259 := h65526;
    (Or.elim h4657 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65528 (p3260 p5114 : Prop)
    (h65527 : p3260)
    (h8659 : (¬ p3260) ∨ p5114)
    : p5114 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5114) := (fun h => hn h);
    let u1 : p3260 := h65527;
    (Or.elim h8659 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65529 (p5114 p6015 : Prop)
    (h65528 : p5114)
    (h13106 : (¬ p5114) ∨ p6015)
    : p6015 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6015) := (fun h => hn h);
    let u1 : p5114 := h65528;
    (Or.elim h13106 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65530 (p482 p488 p2601 : Prop)
    (h3327 : (¬ p482) ∨ p2601)
    (h3328 : (¬ p488) ∨ p2601)
    (h534 : p482 ∨ p488)
    : p2601 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2601) := (fun h => hn h);
    let u1 : (¬ p482) := (Or.elim h3327 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p488) := (Or.elim h3328 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h534 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65531 (p2601 p2602 : Prop)
    (h65530 : p2601)
    (h3345 : (¬ p2601) ∨ p2602)
    : p2602 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2602) := (fun h => hn h);
    let u1 : p2601 := h65530;
    (Or.elim h3345 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65532 (p2602 p4731 : Prop)
    (h65531 : p2602)
    (h7694 : (¬ p2602) ∨ p4731)
    : p4731 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4731) := (fun h => hn h);
    let u1 : p2602 := h65531;
    (Or.elim h7694 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65533 (p4731 p5883 : Prop)
    (h65532 : p4731)
    (h12306 : (¬ p4731) ∨ p5883)
    : p5883 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5883) := (fun h => hn h);
    let u1 : p4731 := h65532;
    (Or.elim h12306 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65534 (p1094 p1100 p3249 : Prop)
    (h4619 : (¬ p1094) ∨ p3249)
    (h4620 : (¬ p1100) ∨ p3249)
    (h1197 : p1094 ∨ p1100)
    : p3249 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3249) := (fun h => hn h);
    let u1 : (¬ p1094) := (Or.elim h4619 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1100) := (Or.elim h4620 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1197 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65535 (p3249 p3250 : Prop)
    (h65534 : p3249)
    (h4637 : (¬ p3249) ∨ p3250)
    : p3250 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3250) := (fun h => hn h);
    let u1 : p3249 := h65534;
    (Or.elim h4637 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65536 (p3250 p5105 : Prop)
    (h65535 : p3250)
    (h8641 : (¬ p3250) ∨ p5105)
    : p5105 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5105) := (fun h => hn h);
    let u1 : p3250 := h65535;
    (Or.elim h8641 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65537 (p5105 p6012 : Prop)
    (h65536 : p5105)
    (h13088 : (¬ p5105) ∨ p6012)
    : p6012 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6012) := (fun h => hn h);
    let u1 : p5105 := h65536;
    (Or.elim h13088 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65538 (p1082 p1088 p3239 : Prop)
    (h4599 : (¬ p1082) ∨ p3239)
    (h4600 : (¬ p1088) ∨ p3239)
    (h1184 : p1082 ∨ p1088)
    : p3239 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3239) := (fun h => hn h);
    let u1 : (¬ p1082) := (Or.elim h4599 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1088) := (Or.elim h4600 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1184 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65539 (p3239 p3240 : Prop)
    (h65538 : p3239)
    (h4617 : (¬ p3239) ∨ p3240)
    : p3240 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3240) := (fun h => hn h);
    let u1 : p3239 := h65538;
    (Or.elim h4617 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65540 (p3240 p5100 : Prop)
    (h65539 : p3240)
    (h8622 : (¬ p3240) ∨ p5100)
    : p5100 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5100) := (fun h => hn h);
    let u1 : p3240 := h65539;
    (Or.elim h8622 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65541 (p5100 p6009 : Prop)
    (h65540 : p5100)
    (h13068 : (¬ p5100) ∨ p6009)
    : p6009 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6009) := (fun h => hn h);
    let u1 : p5100 := h65540;
    (Or.elim h13068 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65542 (p1058 p1064 p3205 : Prop)
    (h4529 : (¬ p1058) ∨ p3205)
    (h4530 : (¬ p1064) ∨ p3205)
    (h1158 : p1058 ∨ p1064)
    : p3205 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3205) := (fun h => hn h);
    let u1 : (¬ p1058) := (Or.elim h4529 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1064) := (Or.elim h4530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1158 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65543 (p3205 p3206 : Prop)
    (h65542 : p3205)
    (h4547 : (¬ p3205) ∨ p3206)
    : p3206 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3206) := (fun h => hn h);
    let u1 : p3205 := h65542;
    (Or.elim h4547 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65544 (p3206 p5088 : Prop)
    (h65543 : p3206)
    (h8584 : (¬ p3206) ∨ p5088)
    : p5088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5088) := (fun h => hn h);
    let u1 : p3206 := h65543;
    (Or.elim h8584 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65546 (p1046 p1052 p3194 : Prop)
    (h4508 : (¬ p1046) ∨ p3194)
    (h4509 : (¬ p1052) ∨ p3194)
    (h1145 : p1046 ∨ p1052)
    : p3194 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3194) := (fun h => hn h);
    let u1 : (¬ p1046) := (Or.elim h4508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1052) := (Or.elim h4509 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1145 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65547 (p3194 p3195 : Prop)
    (h65546 : p3194)
    (h4526 : (¬ p3194) ∨ p3195)
    : p3195 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3195) := (fun h => hn h);
    let u1 : p3194 := h65546;
    (Or.elim h4526 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65548 (p3195 p5080 : Prop)
    (h65547 : p3195)
    (h8565 : (¬ p3195) ∨ p5080)
    : p5080 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5080) := (fun h => hn h);
    let u1 : p3195 := h65547;
    (Or.elim h8565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65549 (p5080 p6003 : Prop)
    (h65548 : p5080)
    (h13029 : (¬ p5080) ∨ p6003)
    : p6003 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6003) := (fun h => hn h);
    let u1 : p5080 := h65548;
    (Or.elim h13029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65550 (p1034 p1040 p3182 : Prop)
    (h4487 : (¬ p1034) ∨ p3182)
    (h4488 : (¬ p1040) ∨ p3182)
    (h1132 : p1034 ∨ p1040)
    : p3182 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3182) := (fun h => hn h);
    let u1 : (¬ p1034) := (Or.elim h4487 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1040) := (Or.elim h4488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1132 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65551 (p3182 p3183 : Prop)
    (h65550 : p3182)
    (h4505 : (¬ p3182) ∨ p3183)
    : p3183 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3183) := (fun h => hn h);
    let u1 : p3182 := h65550;
    (Or.elim h4505 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65552 (p3183 p5072 : Prop)
    (h65551 : p3183)
    (h8547 : (¬ p3183) ∨ p5072)
    : p5072 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5072) := (fun h => hn h);
    let u1 : p3183 := h65551;
    (Or.elim h8547 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65553 (p5072 p6000 : Prop)
    (h65552 : p5072)
    (h13009 : (¬ p5072) ∨ p6000)
    : p6000 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6000) := (fun h => hn h);
    let u1 : p5072 := h65552;
    (Or.elim h13009 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65554 (p146 p152 p2234 : Prop)
    (h2603 : (¬ p146) ∨ p2234)
    (h2604 : (¬ p152) ∨ p2234)
    (h170 : p146 ∨ p152)
    : p2234 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2234) := (fun h => hn h);
    let u1 : (¬ p146) := (Or.elim h2603 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p152) := (Or.elim h2604 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h170 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65555 (p2234 p2235 : Prop)
    (h65554 : p2234)
    (h2621 : (¬ p2234) ∨ p2235)
    : p2235 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2235) := (fun h => hn h);
    let u1 : p2234 := h65554;
    (Or.elim h2621 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65556 (p2235 p4540 : Prop)
    (h65555 : p2235)
    (h7160 : (¬ p2235) ∨ p4540)
    : p4540 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4540) := (fun h => hn h);
    let u1 : p2235 := h65555;
    (Or.elim h7160 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65557 (p1010 p1016 p3149 : Prop)
    (h4419 : (¬ p1010) ∨ p3149)
    (h4420 : (¬ p1016) ∨ p3149)
    (h1106 : p1010 ∨ p1016)
    : p3149 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3149) := (fun h => hn h);
    let u1 : (¬ p1010) := (Or.elim h4419 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1016) := (Or.elim h4420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1106 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65558 (p3149 p3150 : Prop)
    (h65557 : p3149)
    (h4437 : (¬ p3149) ∨ p3150)
    : p3150 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3150) := (fun h => hn h);
    let u1 : p3149 := h65557;
    (Or.elim h4437 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65559 (p3150 p5060 : Prop)
    (h65558 : p3150)
    (h8503 : (¬ p3150) ∨ p5060)
    : p5060 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5060) := (fun h => hn h);
    let u1 : p3150 := h65558;
    (Or.elim h8503 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65560 (p5060 p5997 : Prop)
    (h65559 : p5060)
    (h12989 : (¬ p5060) ∨ p5997)
    : p5997 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5997) := (fun h => hn h);
    let u1 : p5060 := h65559;
    (Or.elim h12989 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65561 (p998 p1004 p3139 : Prop)
    (h4399 : (¬ p998) ∨ p3139)
    (h4400 : (¬ p1004) ∨ p3139)
    (h1093 : p998 ∨ p1004)
    : p3139 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3139) := (fun h => hn h);
    let u1 : (¬ p998) := (Or.elim h4399 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1004) := (Or.elim h4400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1093 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65562 (p3139 p3140 : Prop)
    (h65561 : p3139)
    (h4417 : (¬ p3139) ∨ p3140)
    : p3140 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3140) := (fun h => hn h);
    let u1 : p3139 := h65561;
    (Or.elim h4417 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65563 (p3140 p5054 : Prop)
    (h65562 : p3140)
    (h8486 : (¬ p3140) ∨ p5054)
    : p5054 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5054) := (fun h => hn h);
    let u1 : p3140 := h65562;
    (Or.elim h8486 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65564 (p5054 p5994 : Prop)
    (h65563 : p5054)
    (h12972 : (¬ p5054) ∨ p5994)
    : p5994 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5994) := (fun h => hn h);
    let u1 : p5054 := h65563;
    (Or.elim h12972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65565 (p986 p992 p3129 : Prop)
    (h4379 : (¬ p986) ∨ p3129)
    (h4380 : (¬ p992) ∨ p3129)
    (h1080 : p986 ∨ p992)
    : p3129 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3129) := (fun h => hn h);
    let u1 : (¬ p986) := (Or.elim h4379 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p992) := (Or.elim h4380 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1080 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65566 (p3129 p3130 : Prop)
    (h65565 : p3129)
    (h4397 : (¬ p3129) ∨ p3130)
    : p3130 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3130) := (fun h => hn h);
    let u1 : p3129 := h65565;
    (Or.elim h4397 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65567 (p3130 p5047 : Prop)
    (h65566 : p3130)
    (h8469 : (¬ p3130) ∨ p5047)
    : p5047 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5047) := (fun h => hn h);
    let u1 : p3130 := h65566;
    (Or.elim h8469 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65568 (p5047 p5991 : Prop)
    (h65567 : p5047)
    (h12955 : (¬ p5047) ∨ p5991)
    : p5991 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5991) := (fun h => hn h);
    let u1 : p5047 := h65567;
    (Or.elim h12955 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65569 (p974 p980 p3118 : Prop)
    (h4357 : (¬ p974) ∨ p3118)
    (h4358 : (¬ p980) ∨ p3118)
    (h1067 : p974 ∨ p980)
    : p3118 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3118) := (fun h => hn h);
    let u1 : (¬ p974) := (Or.elim h4357 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p980) := (Or.elim h4358 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1067 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65570 (p3118 p3119 : Prop)
    (h65569 : p3118)
    (h4375 : (¬ p3118) ∨ p3119)
    : p3119 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3119) := (fun h => hn h);
    let u1 : p3118 := h65569;
    (Or.elim h4375 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65571 (p3119 p5041 : Prop)
    (h65570 : p3119)
    (h8452 : (¬ p3119) ∨ p5041)
    : p5041 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5041) := (fun h => hn h);
    let u1 : p3119 := h65570;
    (Or.elim h8452 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65572 (p5041 p5988 : Prop)
    (h65571 : p5041)
    (h12937 : (¬ p5041) ∨ p5988)
    : p5988 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5988) := (fun h => hn h);
    let u1 : p5041 := h65571;
    (Or.elim h12937 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65573 (p962 p968 p3108 : Prop)
    (h4337 : (¬ p962) ∨ p3108)
    (h4338 : (¬ p968) ∨ p3108)
    (h1054 : p962 ∨ p968)
    : p3108 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3108) := (fun h => hn h);
    let u1 : (¬ p962) := (Or.elim h4337 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p968) := (Or.elim h4338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1054 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65574 (p3108 p3109 : Prop)
    (h65573 : p3108)
    (h4355 : (¬ p3108) ∨ p3109)
    : p3109 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3109) := (fun h => hn h);
    let u1 : p3108 := h65573;
    (Or.elim h4355 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65575 (p3109 p5034 : Prop)
    (h65574 : p3109)
    (h8435 : (¬ p3109) ∨ p5034)
    : p5034 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5034) := (fun h => hn h);
    let u1 : p3109 := h65574;
    (Or.elim h8435 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65576 (p5034 p5985 : Prop)
    (h65575 : p5034)
    (h12920 : (¬ p5034) ∨ p5985)
    : p5985 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5985) := (fun h => hn h);
    let u1 : p5034 := h65575;
    (Or.elim h12920 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65577 (p950 p956 p3098 : Prop)
    (h4317 : (¬ p950) ∨ p3098)
    (h4318 : (¬ p956) ∨ p3098)
    (h1041 : p950 ∨ p956)
    : p3098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3098) := (fun h => hn h);
    let u1 : (¬ p950) := (Or.elim h4317 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p956) := (Or.elim h4318 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1041 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65578 (p3098 p3099 : Prop)
    (h65577 : p3098)
    (h4335 : (¬ p3098) ∨ p3099)
    : p3099 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3099) := (fun h => hn h);
    let u1 : p3098 := h65577;
    (Or.elim h4335 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65579 (p3099 p5023 : Prop)
    (h65578 : p3099)
    (h8418 : (¬ p3099) ∨ p5023)
    : p5023 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5023) := (fun h => hn h);
    let u1 : p3099 := h65578;
    (Or.elim h8418 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65580 (p5023 p5982 : Prop)
    (h65579 : p5023)
    (h12902 : (¬ p5023) ∨ p5982)
    : p5982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5982) := (fun h => hn h);
    let u1 : p5023 := h65579;
    (Or.elim h12902 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65581 (p938 p944 p3086 : Prop)
    (h4296 : (¬ p938) ∨ p3086)
    (h4297 : (¬ p944) ∨ p3086)
    (h1028 : p938 ∨ p944)
    : p3086 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3086) := (fun h => hn h);
    let u1 : (¬ p938) := (Or.elim h4296 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p944) := (Or.elim h4297 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1028 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65582 (p3086 p3087 : Prop)
    (h65581 : p3086)
    (h4314 : (¬ p3086) ∨ p3087)
    : p3087 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3087) := (fun h => hn h);
    let u1 : p3086 := h65581;
    (Or.elim h4314 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65583 (p3087 p5013 : Prop)
    (h65582 : p3087)
    (h8399 : (¬ p3087) ∨ p5013)
    : p5013 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5013) := (fun h => hn h);
    let u1 : p3087 := h65582;
    (Or.elim h8399 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65584 (p5013 p5979 : Prop)
    (h65583 : p5013)
    (h12884 : (¬ p5013) ∨ p5979)
    : p5979 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5979) := (fun h => hn h);
    let u1 : p5013 := h65583;
    (Or.elim h12884 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65585 (p626 p632 p2754 : Prop)
    (h3635 : (¬ p626) ∨ p2754)
    (h3636 : (¬ p632) ∨ p2754)
    (h690 : p626 ∨ p632)
    : p2754 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2754) := (fun h => hn h);
    let u1 : (¬ p626) := (Or.elim h3635 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p632) := (Or.elim h3636 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h690 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65586 (p2754 p2755 : Prop)
    (h65585 : p2754)
    (h3653 : (¬ p2754) ∨ p2755)
    : p2755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2755) := (fun h => hn h);
    let u1 : p2754 := h65585;
    (Or.elim h3653 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65587 (p2755 p4821 : Prop)
    (h65586 : p2755)
    (h7915 : (¬ p2755) ∨ p4821)
    : p4821 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4821) := (fun h => hn h);
    let u1 : p2755 := h65586;
    (Or.elim h7915 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65588 (p4821 p5913 : Prop)
    (h65587 : p4821)
    (h12480 : (¬ p4821) ∨ p5913)
    : p5913 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5913) := (fun h => hn h);
    let u1 : p4821 := h65587;
    (Or.elim h12480 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65589 (p470 p476 p2591 : Prop)
    (h3307 : (¬ p470) ∨ p2591)
    (h3308 : (¬ p476) ∨ p2591)
    (h521 : p470 ∨ p476)
    : p2591 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2591) := (fun h => hn h);
    let u1 : (¬ p470) := (Or.elim h3307 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p476) := (Or.elim h3308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h521 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65590 (p2591 p2592 : Prop)
    (h65589 : p2591)
    (h3325 : (¬ p2591) ∨ p2592)
    : p2592 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2592) := (fun h => hn h);
    let u1 : p2591 := h65589;
    (Or.elim h3325 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65591 (p2592 p4725 : Prop)
    (h65590 : p2592)
    (h7677 : (¬ p2592) ∨ p4725)
    : p4725 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4725) := (fun h => hn h);
    let u1 : p2592 := h65590;
    (Or.elim h7677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65592 (p4725 p5880 : Prop)
    (h65591 : p4725)
    (h12289 : (¬ p4725) ∨ p5880)
    : p5880 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5880) := (fun h => hn h);
    let u1 : p4725 := h65591;
    (Or.elim h12289 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65595 (p914 p920 p3066 : Prop)
    (h4256 : (¬ p914) ∨ p3066)
    (h4257 : (¬ p920) ∨ p3066)
    (h1002 : p914 ∨ p920)
    : p3066 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3066) := (fun h => hn h);
    let u1 : (¬ p914) := (Or.elim h4256 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p920) := (Or.elim h4257 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1002 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65596 (p3066 p3067 : Prop)
    (h65595 : p3066)
    (h4274 : (¬ p3066) ∨ p3067)
    : p3067 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3067) := (fun h => hn h);
    let u1 : p3066 := h65595;
    (Or.elim h4274 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65597 (p3067 p4999 : Prop)
    (h65596 : p3067)
    (h8364 : (¬ p3067) ∨ p4999)
    : p4999 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4999) := (fun h => hn h);
    let u1 : p3067 := h65596;
    (Or.elim h8364 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65598 (p4999 p5973 : Prop)
    (h65597 : p4999)
    (h12849 : (¬ p4999) ∨ p5973)
    : p5973 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5973) := (fun h => hn h);
    let u1 : p4999 := h65597;
    (Or.elim h12849 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65599 (p2103 p2608 p3073 p3439 p3857 p3860 p4261 p4340 p4353 p4416 p4444 p4999 p5000 p5003 p5312 p6055 p6079 : Prop)
    (h65597 : p4999)
    (h13506 : p4353 ∨ p6079)
    (h13504 : p5312 ∨ p6079)
    (h13333 : p4416 ∨ p6055)
    (h13335 : p3860 ∨ p6055)
    (h13336 : p3439 ∨ p6055)
    (h45633 : (¬ p2608) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444))
    (h30173 : p2103 ∨ (¬ p3439) ∨ (¬ p4353))
    (h8351 : p4261 ∨ (¬ p5000))
    (h6582 : (¬ p2103) ∨ p3857 ∨ (¬ p4340))
    (h8363 : (¬ p4999) ∨ p5000 ∨ p5003)
    (h42229 : (¬ p2608) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4416) ∨ (¬ p5312))
    (h8357 : p3073 ∨ (¬ p5003))
    : p6055 ∨ (¬ p4444) ∨ (¬ p2608) ∨ p6079 ∨ (¬ p4340) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6055) := (fun h => hn (Or.inl h));
    let u1 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p6079) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4999 := h65597;
    let u6 : p4353 := (Or.elim h13506 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p5312 := (Or.elim h13504 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4416 := (Or.elim h13333 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3860 := (Or.elim h13335 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3439 := (Or.elim h13336 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : (¬ p4261) := (Or.elim h45633 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    let u12 : p2103 := (Or.elim h30173 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (False.elim (r1 u6))))));
    let u13 : (¬ p5000) := (Or.elim h8351 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : p3857 := (Or.elim h6582 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u4))))));
    let u15 : p5003 := (Or.elim h8363 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => r1))));
    let u16 : (¬ p3073) := (Or.elim h42229 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u7))))))))));
    (Or.elim h8357 (fun q0 => (False.elim (u16 q0))) (fun r0 => (False.elim (r0 u15)))))

theorem step65600 (p566 p572 p2689 : Prop)
    (h3504 : (¬ p566) ∨ p2689)
    (h3505 : (¬ p572) ∨ p2689)
    (h625 : p566 ∨ p572)
    : p2689 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2689) := (fun h => hn h);
    let u1 : (¬ p566) := (Or.elim h3504 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p572) := (Or.elim h3505 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h625 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65601 (p2689 p2690 : Prop)
    (h65600 : p2689)
    (h3522 : (¬ p2689) ∨ p2690)
    : p2690 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2690) := (fun h => hn h);
    let u1 : p2689 := h65600;
    (Or.elim h3522 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65602 (p2690 p4784 : Prop)
    (h65601 : p2690)
    (h7818 : (¬ p2690) ∨ p4784)
    : p4784 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4784) := (fun h => hn h);
    let u1 : p2690 := h65601;
    (Or.elim h7818 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65603 (p4784 p5901 : Prop)
    (h65602 : p4784)
    (h12409 : (¬ p4784) ∨ p5901)
    : p5901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5901) := (fun h => hn h);
    let u1 : p4784 := h65602;
    (Or.elim h12409 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65604 (p506 p512 p2623 : Prop)
    (h3371 : (¬ p506) ∨ p2623)
    (h3372 : (¬ p512) ∨ p2623)
    (h560 : p506 ∨ p512)
    : p2623 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2623) := (fun h => hn h);
    let u1 : (¬ p506) := (Or.elim h3371 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p512) := (Or.elim h3372 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h560 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65605 (p2623 p2624 : Prop)
    (h65604 : p2623)
    (h3389 : (¬ p2623) ∨ p2624)
    : p2624 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2624) := (fun h => hn h);
    let u1 : p2623 := h65604;
    (Or.elim h3389 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65606 (p2624 p4747 : Prop)
    (h65605 : p2624)
    (h7728 : (¬ p2624) ∨ p4747)
    : p4747 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4747) := (fun h => hn h);
    let u1 : p2624 := h65605;
    (Or.elim h7728 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65607 (p4747 p5889 : Prop)
    (h65606 : p4747)
    (h12340 : (¬ p4747) ∨ p5889)
    : p5889 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5889) := (fun h => hn h);
    let u1 : p4747 := h65606;
    (Or.elim h12340 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65608 (p13 p19 p2091 : Prop)
    (h2316 : (¬ p13) ∨ p2091)
    (h2317 : (¬ p19) ∨ p2091)
    (h26 : p13 ∨ p19)
    : p2091 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2091) := (fun h => hn h);
    let u1 : (¬ p13) := (Or.elim h2316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p19) := (Or.elim h2317 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h26 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65609 (p2091 p2092 : Prop)
    (h65608 : p2091)
    (h2334 : (¬ p2091) ∨ p2092)
    : p2092 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2092) := (fun h => hn h);
    let u1 : p2091 := h65608;
    (Or.elim h2334 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65610 (p2092 p4464 : Prop)
    (h65609 : p2092)
    (h6964 : (¬ p2092) ∨ p4464)
    : p4464 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4464) := (fun h => hn h);
    let u1 : p2092 := h65609;
    (Or.elim h6964 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65611 (p614 p620 p2730 : Prop)
    (h3586 : (¬ p614) ∨ p2730)
    (h3587 : (¬ p620) ∨ p2730)
    (h677 : p614 ∨ p620)
    : p2730 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2730) := (fun h => hn h);
    let u1 : (¬ p614) := (Or.elim h3586 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p620) := (Or.elim h3587 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h677 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65612 (p2730 p2731 : Prop)
    (h65611 : p2730)
    (h3604 : (¬ p2730) ∨ p2731)
    : p2731 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2731) := (fun h => hn h);
    let u1 : p2730 := h65611;
    (Or.elim h3604 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65613 (p2731 p4815 : Prop)
    (h65612 : p2731)
    (h7876 : (¬ p2731) ∨ p4815)
    : p4815 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4815) := (fun h => hn h);
    let u1 : p2731 := h65612;
    (Or.elim h7876 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65615 (p494 p500 p2612 : Prop)
    (h3349 : (¬ p494) ∨ p2612)
    (h3350 : (¬ p500) ∨ p2612)
    (h547 : p494 ∨ p500)
    : p2612 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2612) := (fun h => hn h);
    let u1 : (¬ p494) := (Or.elim h3349 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p500) := (Or.elim h3350 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h547 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65616 (p2612 p2613 : Prop)
    (h65615 : p2612)
    (h3367 : (¬ p2612) ∨ p2613)
    : p2613 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2613) := (fun h => hn h);
    let u1 : p2612 := h65615;
    (Or.elim h3367 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65617 (p2613 p4738 : Prop)
    (h65616 : p2613)
    (h7711 : (¬ p2613) ∨ p4738)
    : p4738 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4738) := (fun h => hn h);
    let u1 : p2613 := h65616;
    (Or.elim h7711 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65618 (p4738 p5886 : Prop)
    (h65617 : p4738)
    (h12323 : (¬ p4738) ∨ p5886)
    : p5886 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5886) := (fun h => hn h);
    let u1 : p4738 := h65617;
    (Or.elim h12323 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65620 (p578 p584 p2700 : Prop)
    (h3526 : (¬ p578) ∨ p2700)
    (h3527 : (¬ p584) ∨ p2700)
    (h638 : p578 ∨ p584)
    : p2700 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2700) := (fun h => hn h);
    let u1 : (¬ p578) := (Or.elim h3526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p584) := (Or.elim h3527 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h638 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65621 (p2700 p2701 : Prop)
    (h65620 : p2700)
    (h3544 : (¬ p2700) ∨ p2701)
    : p2701 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2701) := (fun h => hn h);
    let u1 : p2700 := h65620;
    (Or.elim h3544 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65622 (p2701 p4791 : Prop)
    (h65621 : p2701)
    (h7836 : (¬ p2701) ∨ p4791)
    : p4791 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4791) := (fun h => hn h);
    let u1 : p2701 := h65621;
    (Or.elim h7836 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65623 (p4791 p5904 : Prop)
    (h65622 : p4791)
    (h12427 : (¬ p4791) ∨ p5904)
    : p5904 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5904) := (fun h => hn h);
    let u1 : p4791 := h65622;
    (Or.elim h12427 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65624 (p590 p596 p2710 : Prop)
    (h3546 : (¬ p590) ∨ p2710)
    (h3547 : (¬ p596) ∨ p2710)
    (h651 : p590 ∨ p596)
    : p2710 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2710) := (fun h => hn h);
    let u1 : (¬ p590) := (Or.elim h3546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p596) := (Or.elim h3547 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h651 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65625 (p2710 p2711 : Prop)
    (h65624 : p2710)
    (h3564 : (¬ p2710) ∨ p2711)
    : p2711 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2711) := (fun h => hn h);
    let u1 : p2710 := h65624;
    (Or.elim h3564 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65626 (p2711 p4798 : Prop)
    (h65625 : p2711)
    (h7853 : (¬ p2711) ∨ p4798)
    : p4798 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4798) := (fun h => hn h);
    let u1 : p2711 := h65625;
    (Or.elim h7853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65627 (p4798 p5907 : Prop)
    (h65626 : p4798)
    (h12445 : (¬ p4798) ∨ p5907)
    : p5907 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5907) := (fun h => hn h);
    let u1 : p4798 := h65626;
    (Or.elim h12445 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65628 (p734 p740 p2863 : Prop)
    (h3852 : (¬ p734) ∨ p2863)
    (h3853 : (¬ p740) ∨ p2863)
    (h807 : p734 ∨ p740)
    : p2863 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2863) := (fun h => hn h);
    let u1 : (¬ p734) := (Or.elim h3852 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p740) := (Or.elim h3853 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h807 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65629 (p2863 p2864 : Prop)
    (h65628 : p2863)
    (h3870 : (¬ p2863) ∨ p2864)
    : p2864 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2864) := (fun h => hn h);
    let u1 : p2863 := h65628;
    (Or.elim h3870 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65630 (p2864 p4892 : Prop)
    (h65629 : p2864)
    (h8081 : (¬ p2864) ∨ p4892)
    : p4892 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4892) := (fun h => hn h);
    let u1 : p2864 := h65629;
    (Or.elim h8081 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65631 (p4892 p5937 : Prop)
    (h65630 : p4892)
    (h12626 : (¬ p4892) ∨ p5937)
    : p5937 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5937) := (fun h => hn h);
    let u1 : p4892 := h65630;
    (Or.elim h12626 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65632 (p926 p932 p3076 : Prop)
    (h4276 : (¬ p926) ∨ p3076)
    (h4277 : (¬ p932) ∨ p3076)
    (h1015 : p926 ∨ p932)
    : p3076 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3076) := (fun h => hn h);
    let u1 : (¬ p926) := (Or.elim h4276 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p932) := (Or.elim h4277 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1015 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65633 (p3076 p3077 : Prop)
    (h65632 : p3076)
    (h4294 : (¬ p3076) ∨ p3077)
    : p3077 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3077) := (fun h => hn h);
    let u1 : p3076 := h65632;
    (Or.elim h4294 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65634 (p3077 p5006 : Prop)
    (h65633 : p3077)
    (h8382 : (¬ p3077) ∨ p5006)
    : p5006 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5006) := (fun h => hn h);
    let u1 : p3077 := h65633;
    (Or.elim h8382 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65635 (p5006 p5976 : Prop)
    (h65634 : p5006)
    (h12867 : (¬ p5006) ∨ p5976)
    : p5976 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5976) := (fun h => hn h);
    let u1 : p5006 := h65634;
    (Or.elim h12867 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65636 (p902 p908 p3056 : Prop)
    (h4236 : (¬ p902) ∨ p3056)
    (h4237 : (¬ p908) ∨ p3056)
    (h989 : p902 ∨ p908)
    : p3056 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3056) := (fun h => hn h);
    let u1 : (¬ p902) := (Or.elim h4236 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p908) := (Or.elim h4237 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h989 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65637 (p3056 p3057 : Prop)
    (h65636 : p3056)
    (h4254 : (¬ p3056) ∨ p3057)
    : p3057 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3057) := (fun h => hn h);
    let u1 : p3056 := h65636;
    (Or.elim h4254 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65638 (p3057 p4991 : Prop)
    (h65637 : p3057)
    (h8347 : (¬ p3057) ∨ p4991)
    : p4991 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4991) := (fun h => hn h);
    let u1 : p3057 := h65637;
    (Or.elim h8347 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65639 (p4991 p5970 : Prop)
    (h65638 : p4991)
    (h12832 : (¬ p4991) ∨ p5970)
    : p5970 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5970) := (fun h => hn h);
    let u1 : p4991 := h65638;
    (Or.elim h12832 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65640 (p890 p896 p3044 : Prop)
    (h4215 : (¬ p890) ∨ p3044)
    (h4216 : (¬ p896) ∨ p3044)
    (h976 : p890 ∨ p896)
    : p3044 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3044) := (fun h => hn h);
    let u1 : (¬ p890) := (Or.elim h4215 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p896) := (Or.elim h4216 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h976 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65641 (p3044 p3045 : Prop)
    (h65640 : p3044)
    (h4233 : (¬ p3044) ∨ p3045)
    : p3045 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3045) := (fun h => hn h);
    let u1 : p3044 := h65640;
    (Or.elim h4233 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65642 (p3045 p4982 : Prop)
    (h65641 : p3045)
    (h8328 : (¬ p3045) ∨ p4982)
    : p4982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4982) := (fun h => hn h);
    let u1 : p3045 := h65641;
    (Or.elim h8328 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65643 (p4982 p5967 : Prop)
    (h65642 : p4982)
    (h12815 : (¬ p4982) ∨ p5967)
    : p5967 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5967) := (fun h => hn h);
    let u1 : p4982 := h65642;
    (Or.elim h12815 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65644 (p38 p44 p2125 : Prop)
    (h2386 : (¬ p38) ∨ p2125)
    (h2387 : (¬ p44) ∨ p2125)
    (h53 : p38 ∨ p44)
    : p2125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2125) := (fun h => hn h);
    let u1 : (¬ p38) := (Or.elim h2386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p44) := (Or.elim h2387 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65645 (p2125 p2126 : Prop)
    (h65644 : p2125)
    (h2404 : (¬ p2125) ∨ p2126)
    : p2126 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2126) := (fun h => hn h);
    let u1 : p2125 := h65644;
    (Or.elim h2404 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65646 (p2126 p4478 : Prop)
    (h65645 : p2126)
    (h7002 : (¬ p2126) ∨ p4478)
    : p4478 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4478) := (fun h => hn h);
    let u1 : p2126 := h65645;
    (Or.elim h7002 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65647 (p746 p752 p2874 : Prop)
    (h3874 : (¬ p746) ∨ p2874)
    (h3875 : (¬ p752) ∨ p2874)
    (h820 : p746 ∨ p752)
    : p2874 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2874) := (fun h => hn h);
    let u1 : (¬ p746) := (Or.elim h3874 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p752) := (Or.elim h3875 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h820 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65648 (p2874 p2875 : Prop)
    (h65647 : p2874)
    (h3892 : (¬ p2874) ∨ p2875)
    : p2875 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2875) := (fun h => hn h);
    let u1 : p2874 := h65647;
    (Or.elim h3892 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65649 (p2875 p4899 : Prop)
    (h65648 : p2875)
    (h8099 : (¬ p2875) ∨ p4899)
    : p4899 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4899) := (fun h => hn h);
    let u1 : p2875 := h65648;
    (Or.elim h8099 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65650 (p4899 p5940 : Prop)
    (h65649 : p4899)
    (h12645 : (¬ p4899) ∨ p5940)
    : p5940 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5940) := (fun h => hn h);
    let u1 : p4899 := h65649;
    (Or.elim h12645 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65651 (p866 p872 p3009 : Prop)
    (h4142 : (¬ p866) ∨ p3009)
    (h4143 : (¬ p872) ∨ p3009)
    (h950 : p866 ∨ p872)
    : p3009 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3009) := (fun h => hn h);
    let u1 : (¬ p866) := (Or.elim h4142 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p872) := (Or.elim h4143 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h950 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65652 (p3009 p3010 : Prop)
    (h65651 : p3009)
    (h4160 : (¬ p3009) ∨ p3010)
    : p3010 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3010) := (fun h => hn h);
    let u1 : p3009 := h65651;
    (Or.elim h4160 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65653 (p3010 p4970 : Prop)
    (h65652 : p3010)
    (h8287 : (¬ p3010) ∨ p4970)
    : p4970 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4970) := (fun h => hn h);
    let u1 : p3010 := h65652;
    (Or.elim h8287 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65654 (p4970 p5964 : Prop)
    (h65653 : p4970)
    (h12794 : (¬ p4970) ∨ p5964)
    : p5964 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5964) := (fun h => hn h);
    let u1 : p4970 := h65653;
    (Or.elim h12794 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65655 (p854 p860 p2998 : Prop)
    (h4120 : (¬ p854) ∨ p2998)
    (h4121 : (¬ p860) ∨ p2998)
    (h937 : p854 ∨ p860)
    : p2998 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2998) := (fun h => hn h);
    let u1 : (¬ p854) := (Or.elim h4120 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p860) := (Or.elim h4121 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h937 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65656 (p2998 p2999 : Prop)
    (h65655 : p2998)
    (h4138 : (¬ p2998) ∨ p2999)
    : p2999 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2999) := (fun h => hn h);
    let u1 : p2998 := h65655;
    (Or.elim h4138 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65657 (p2999 p4961 : Prop)
    (h65656 : p2999)
    (h8270 : (¬ p2999) ∨ p4961)
    : p4961 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4961) := (fun h => hn h);
    let u1 : p2999 := h65656;
    (Or.elim h8270 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65658 (p4961 p5961 : Prop)
    (h65657 : p4961)
    (h12774 : (¬ p4961) ∨ p5961)
    : p5961 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5961) := (fun h => hn h);
    let u1 : p4961 := h65657;
    (Or.elim h12774 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65659 (p842 p848 p2985 : Prop)
    (h4097 : (¬ p842) ∨ p2985)
    (h4098 : (¬ p848) ∨ p2985)
    (h924 : p842 ∨ p848)
    : p2985 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2985) := (fun h => hn h);
    let u1 : (¬ p842) := (Or.elim h4097 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p848) := (Or.elim h4098 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h924 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65660 (p2985 p2986 : Prop)
    (h65659 : p2985)
    (h4115 : (¬ p2985) ∨ p2986)
    : p2986 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2986) := (fun h => hn h);
    let u1 : p2985 := h65659;
    (Or.elim h4115 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65661 (p2986 p4955 : Prop)
    (h65660 : p2986)
    (h8253 : (¬ p2986) ∨ p4955)
    : p4955 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4955) := (fun h => hn h);
    let u1 : p2986 := h65660;
    (Or.elim h8253 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65662 (p4955 p5958 : Prop)
    (h65661 : p4955)
    (h12752 : (¬ p4955) ∨ p5958)
    : p5958 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5958) := (fun h => hn h);
    let u1 : p4955 := h65661;
    (Or.elim h12752 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65663 (p518 p524 p2634 : Prop)
    (h3393 : (¬ p518) ∨ p2634)
    (h3394 : (¬ p524) ∨ p2634)
    (h573 : p518 ∨ p524)
    : p2634 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2634) := (fun h => hn h);
    let u1 : (¬ p518) := (Or.elim h3393 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p524) := (Or.elim h3394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h573 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65664 (p2634 p2635 : Prop)
    (h65663 : p2634)
    (h3411 : (¬ p2634) ∨ p2635)
    : p2635 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2635) := (fun h => hn h);
    let u1 : p2634 := h65663;
    (Or.elim h3411 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65665 (p2635 p4754 : Prop)
    (h65664 : p2635)
    (h7746 : (¬ p2635) ∨ p4754)
    : p4754 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4754) := (fun h => hn h);
    let u1 : p2635 := h65664;
    (Or.elim h7746 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65666 (p4754 p5892 : Prop)
    (h65665 : p4754)
    (h12358 : (¬ p4754) ∨ p5892)
    : p5892 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5892) := (fun h => hn h);
    let u1 : p4754 := h65665;
    (Or.elim h12358 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65667 (p830 p836 p2975 : Prop)
    (h4077 : (¬ p830) ∨ p2975)
    (h4078 : (¬ p836) ∨ p2975)
    (h911 : p830 ∨ p836)
    : p2975 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2975) := (fun h => hn h);
    let u1 : (¬ p830) := (Or.elim h4077 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p836) := (Or.elim h4078 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h911 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65668 (p2975 p2976 : Prop)
    (h65667 : p2975)
    (h4095 : (¬ p2975) ∨ p2976)
    : p2976 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2976) := (fun h => hn h);
    let u1 : p2975 := h65667;
    (Or.elim h4095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65669 (p2976 p4945 : Prop)
    (h65668 : p2976)
    (h8236 : (¬ p2976) ∨ p4945)
    : p4945 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4945) := (fun h => hn h);
    let u1 : p2976 := h65668;
    (Or.elim h8236 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65670 (p4945 p5955 : Prop)
    (h65669 : p4945)
    (h12734 : (¬ p4945) ∨ p5955)
    : p5955 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5955) := (fun h => hn h);
    let u1 : p4945 := h65669;
    (Or.elim h12734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65671 (p134 p140 p2223 : Prop)
    (h2581 : (¬ p134) ∨ p2223)
    (h2582 : (¬ p140) ∨ p2223)
    (h157 : p134 ∨ p140)
    : p2223 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2223) := (fun h => hn h);
    let u1 : (¬ p134) := (Or.elim h2581 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p140) := (Or.elim h2582 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h157 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65672 (p2223 p2224 : Prop)
    (h65671 : p2223)
    (h2599 : (¬ p2223) ∨ p2224)
    : p2224 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2224) := (fun h => hn h);
    let u1 : p2223 := h65671;
    (Or.elim h2599 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65673 (p2224 p4534 : Prop)
    (h65672 : p2224)
    (h7155 : (¬ p2224) ∨ p4534)
    : p4534 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4534) := (fun h => hn h);
    let u1 : p2224 := h65672;
    (Or.elim h7155 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65674 (p4534 p5811 : Prop)
    (h65673 : p4534)
    (h11885 : (¬ p4534) ∨ p5811)
    : p5811 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5811) := (fun h => hn h);
    let u1 : p4534 := h65673;
    (Or.elim h11885 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65675 (p818 p824 p2965 : Prop)
    (h4057 : (¬ p818) ∨ p2965)
    (h4058 : (¬ p824) ∨ p2965)
    (h898 : p818 ∨ p824)
    : p2965 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2965) := (fun h => hn h);
    let u1 : (¬ p818) := (Or.elim h4057 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p824) := (Or.elim h4058 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h898 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65676 (p2965 p2966 : Prop)
    (h65675 : p2965)
    (h4075 : (¬ p2965) ∨ p2966)
    : p2966 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2966) := (fun h => hn h);
    let u1 : p2965 := h65675;
    (Or.elim h4075 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65677 (p2966 p4936 : Prop)
    (h65676 : p2966)
    (h8219 : (¬ p2966) ∨ p4936)
    : p4936 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4936) := (fun h => hn h);
    let u1 : p2966 := h65676;
    (Or.elim h8219 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65678 (p4936 p5952 : Prop)
    (h65677 : p4936)
    (h12716 : (¬ p4936) ∨ p5952)
    : p5952 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5952) := (fun h => hn h);
    let u1 : p4936 := h65677;
    (Or.elim h12716 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65679 (p758 p764 p2884 : Prop)
    (h3894 : (¬ p758) ∨ p2884)
    (h3895 : (¬ p764) ∨ p2884)
    (h833 : p758 ∨ p764)
    : p2884 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2884) := (fun h => hn h);
    let u1 : (¬ p758) := (Or.elim h3894 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p764) := (Or.elim h3895 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h833 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65680 (p2884 p2885 : Prop)
    (h65679 : p2884)
    (h3912 : (¬ p2884) ∨ p2885)
    : p2885 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2885) := (fun h => hn h);
    let u1 : p2884 := h65679;
    (Or.elim h3912 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65681 (p2885 p4907 : Prop)
    (h65680 : p2885)
    (h8117 : (¬ p2885) ∨ p4907)
    : p4907 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4907) := (fun h => hn h);
    let u1 : p2885 := h65680;
    (Or.elim h8117 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65682 (p4907 p5943 : Prop)
    (h65681 : p4907)
    (h12662 : (¬ p4907) ∨ p5943)
    : p5943 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5943) := (fun h => hn h);
    let u1 : p4907 := h65681;
    (Or.elim h12662 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65685 (p806 p812 p2939 : Prop)
    (h4006 : (¬ p806) ∨ p2939)
    (h4007 : (¬ p812) ∨ p2939)
    (h885 : p806 ∨ p812)
    : p2939 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2939) := (fun h => hn h);
    let u1 : (¬ p806) := (Or.elim h4006 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p812) := (Or.elim h4007 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h885 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65686 (p2939 p2940 : Prop)
    (h65685 : p2939)
    (h4024 : (¬ p2939) ∨ p2940)
    : p2940 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2940) := (fun h => hn h);
    let u1 : p2939 := h65685;
    (Or.elim h4024 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65687 (p2940 p4931 : Prop)
    (h65686 : p2940)
    (h8183 : (¬ p2940) ∨ p4931)
    : p4931 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4931) := (fun h => hn h);
    let u1 : p2940 := h65686;
    (Or.elim h8183 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65688 (p62 p68 p2159 : Prop)
    (h2456 : (¬ p62) ∨ p2159)
    (h2457 : (¬ p68) ∨ p2159)
    (h79 : p62 ∨ p68)
    : p2159 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2159) := (fun h => hn h);
    let u1 : (¬ p62) := (Or.elim h2456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p68) := (Or.elim h2457 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65689 (p2159 p2160 : Prop)
    (h65688 : p2159)
    (h2474 : (¬ p2159) ∨ p2160)
    : p2160 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2160) := (fun h => hn h);
    let u1 : p2159 := h65688;
    (Or.elim h2474 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65690 (p2160 p4490 : Prop)
    (h65689 : p2160)
    (h7052 : (¬ p2160) ∨ p4490)
    : p4490 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4490) := (fun h => hn h);
    let u1 : p2160 := h65689;
    (Or.elim h7052 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65691 (p4490 p5793 : Prop)
    (h65690 : p4490)
    (h11781 : (¬ p4490) ∨ p5793)
    : p5793 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5793) := (fun h => hn h);
    let u1 : p4490 := h65690;
    (Or.elim h11781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65692 (p362 p368 p2452 : Prop)
    (h3035 : (¬ p362) ∨ p2452)
    (h3036 : (¬ p368) ∨ p2452)
    (h404 : p362 ∨ p368)
    : p2452 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2452) := (fun h => hn h);
    let u1 : (¬ p362) := (Or.elim h3035 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p368) := (Or.elim h3036 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h404 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65693 (p2452 p2453 : Prop)
    (h65692 : p2452)
    (h3053 : (¬ p2452) ∨ p2453)
    : p2453 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2453) := (fun h => hn h);
    let u1 : p2452 := h65692;
    (Or.elim h3053 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65694 (p2453 p4664 : Prop)
    (h65693 : p2453)
    (h7494 : (¬ p2453) ∨ p4664)
    : p4664 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4664) := (fun h => hn h);
    let u1 : p2453 := h65693;
    (Or.elim h7494 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65695 (p4664 p5862 : Prop)
    (h65694 : p4664)
    (h12183 : (¬ p4664) ∨ p5862)
    : p5862 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5862) := (fun h => hn h);
    let u1 : p4664 := h65694;
    (Or.elim h12183 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65697 (p698 p704 p2832 : Prop)
    (h3790 : (¬ p698) ∨ p2832)
    (h3791 : (¬ p704) ∨ p2832)
    (h768 : p698 ∨ p704)
    : p2832 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2832) := (fun h => hn h);
    let u1 : (¬ p698) := (Or.elim h3790 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p704) := (Or.elim h3791 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h768 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65698 (p2832 p2833 : Prop)
    (h65697 : p2832)
    (h3808 : (¬ p2832) ∨ p2833)
    : p2833 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2833) := (fun h => hn h);
    let u1 : p2832 := h65697;
    (Or.elim h3808 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65699 (p2833 p4872 : Prop)
    (h65698 : p2833)
    (h8030 : (¬ p2833) ∨ p4872)
    : p4872 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4872) := (fun h => hn h);
    let u1 : p2833 := h65698;
    (Or.elim h8030 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65700 (p4872 p5928 : Prop)
    (h65699 : p4872)
    (h12574 : (¬ p4872) ∨ p5928)
    : p5928 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5928) := (fun h => hn h);
    let u1 : p4872 := h65699;
    (Or.elim h12574 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65702 (p2098 p2132 p2135 p2138 p2142 p2166 p2191 p2619 p2753 p3537 p4188 p4242 p4243 p4478 p4731 p4732 p4735 p4737 p4743 p4872 p4873 p4874 p4875 p4876 p5310 p5311 p5314 : Prop)
    (h65699 : p4872)
    (h65444 : p5310)
    (h65646 : p4478)
    (h65532 : p4731)
    (h9935 : (¬ p2166) ∨ (¬ p2191))
    (h7702 : p4188 ∨ (¬ p4743))
    (h7704 : p2619 ∨ (¬ p4743))
    (h6718 : p2166 ∨ (¬ p2619) ∨ (¬ p4243))
    (h8021 : p4243 ∨ (¬ p4876))
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    (h8015 : (¬ p4873) ∨ p4874)
    (h8019 : (¬ p4873) ∨ p4875)
    (h25955 : p2166 ∨ (¬ p3537) ∨ (¬ p4188) ∨ (¬ p4874))
    (h42331 : (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2191) ∨ (¬ p4188) ∨ (¬ p4875))
    (h9067 : p3537 ∨ (¬ p5314))
    (h2408 : (¬ p2135) ∨ p2138)
    (h9073 : (¬ p5310) ∨ p5311 ∨ p5314)
    (h7001 : p2135 ∨ p2142 ∨ (¬ p4478))
    (h9061 : p4242 ∨ (¬ p5311))
    (h2422 : p2132 ∨ (¬ p2142))
    (h6369 : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p4242))
    (h49512 : (¬ p2132) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p4737) ∨ (¬ p4874))
    (h7680 : p2753 ∨ (¬ p4732))
    (h7689 : (¬ p4735) ∨ p4737)
    (h7693 : (¬ p4731) ∨ p4732 ∨ p4735)
    : (¬ p4743) ∨ (¬ p2098) ∨ (¬ p2191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4872 := h65699;
    let u4 : p5310 := h65444;
    let u5 : p4478 := h65646;
    let u6 : p4731 := h65532;
    let u7 : (¬ p2166) := (Or.elim h9935 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : p4188 := (Or.elim h7702 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : p2619 := (Or.elim h7704 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : (¬ p4243) := (Or.elim h6718 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => r1))));
    let u11 : (¬ p4876) := (Or.elim h8021 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u12 : p4873 := (Or.elim h8029 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u11 r1))))));
    let u13 : p4874 := (Or.elim h8015 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u14 : p4875 := (Or.elim h8019 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u15 : (¬ p3537) := (Or.elim h25955 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (False.elim (r2 u13))))))));
    let u16 : (¬ p2138) := (Or.elim h42331 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u14))))))))));
    let u17 : (¬ p5314) := (Or.elim h9067 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : (¬ p2135) := (Or.elim h2408 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u19 : p5311 := (Or.elim h9073 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u17 r1))))));
    let u20 : p2142 := (Or.elim h7001 (fun q0 => (False.elim (u18 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u21 : p4242 := (Or.elim h9061 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    let u22 : p2132 := (Or.elim h2422 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u23 : (¬ p2753) := (Or.elim h6369 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u21))))));
    let u24 : (¬ p4737) := (Or.elim h49512 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u13))))))))));
    let u25 : (¬ p4732) := (Or.elim h7680 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u26 : (¬ p4735) := (Or.elim h7689 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    (Or.elim h7693 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u25 q1))) (fun r1 => (False.elim (u26 r1)))))))

theorem step65703 (p122 p128 p2213 : Prop)
    (h2561 : (¬ p122) ∨ p2213)
    (h2562 : (¬ p128) ∨ p2213)
    (h144 : p122 ∨ p128)
    : p2213 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2213) := (fun h => hn h);
    let u1 : (¬ p122) := (Or.elim h2561 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p128) := (Or.elim h2562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h144 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65704 (p2213 p2214 : Prop)
    (h65703 : p2213)
    (h2579 : (¬ p2213) ∨ p2214)
    : p2214 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2214) := (fun h => hn h);
    let u1 : p2213 := h65703;
    (Or.elim h2579 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65705 (p2214 p4526 : Prop)
    (h65704 : p2214)
    (h7137 : (¬ p2214) ∨ p4526)
    : p4526 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4526) := (fun h => hn h);
    let u1 : p2214 := h65704;
    (Or.elim h7137 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65706 (p4526 p5808 : Prop)
    (h65705 : p4526)
    (h11868 : (¬ p4526) ∨ p5808)
    : p5808 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5808) := (fun h => hn h);
    let u1 : p4526 := h65705;
    (Or.elim h11868 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65707 (p554 p560 p2678 : Prop)
    (h3482 : (¬ p554) ∨ p2678)
    (h3483 : (¬ p560) ∨ p2678)
    (h612 : p554 ∨ p560)
    : p2678 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2678) := (fun h => hn h);
    let u1 : (¬ p554) := (Or.elim h3482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p560) := (Or.elim h3483 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h612 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65708 (p2678 p2679 : Prop)
    (h65707 : p2678)
    (h3500 : (¬ p2678) ∨ p2679)
    : p2679 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2679) := (fun h => hn h);
    let u1 : p2678 := h65707;
    (Or.elim h3500 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65709 (p2679 p4775 : Prop)
    (h65708 : p2679)
    (h7801 : (¬ p2679) ∨ p4775)
    : p4775 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4775) := (fun h => hn h);
    let u1 : p2679 := h65708;
    (Or.elim h7801 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65710 (p4775 p5898 : Prop)
    (h65709 : p4775)
    (h12392 : (¬ p4775) ∨ p5898)
    : p5898 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5898) := (fun h => hn h);
    let u1 : p4775 := h65709;
    (Or.elim h12392 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65711 (p1550 p1556 p3760 : Prop)
    (h5513 : (¬ p1550) ∨ p3760)
    (h5514 : (¬ p1556) ∨ p3760)
    (h1691 : p1550 ∨ p1556)
    : p3760 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3760) := (fun h => hn h);
    let u1 : (¬ p1550) := (Or.elim h5513 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1556) := (Or.elim h5514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1691 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65712 (p3760 p3761 : Prop)
    (h65711 : p3760)
    (h5531 : (¬ p3760) ∨ p3761)
    : p3761 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3761) := (fun h => hn h);
    let u1 : p3760 := h65711;
    (Or.elim h5531 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65713 (p3761 p5462 : Prop)
    (h65712 : p3761)
    (h9455 : (¬ p3761) ∨ p5462)
    : p5462 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5462) := (fun h => hn h);
    let u1 : p3761 := h65712;
    (Or.elim h9455 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65714 (p686 p692 p2822 : Prop)
    (h3770 : (¬ p686) ∨ p2822)
    (h3771 : (¬ p692) ∨ p2822)
    (h755 : p686 ∨ p692)
    : p2822 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2822) := (fun h => hn h);
    let u1 : (¬ p686) := (Or.elim h3770 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p692) := (Or.elim h3771 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h755 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65715 (p2822 p2823 : Prop)
    (h65714 : p2822)
    (h3788 : (¬ p2822) ∨ p2823)
    : p2823 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2823) := (fun h => hn h);
    let u1 : p2822 := h65714;
    (Or.elim h3788 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65716 (p2823 p4864 : Prop)
    (h65715 : p2823)
    (h8013 : (¬ p2823) ∨ p4864)
    : p4864 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4864) := (fun h => hn h);
    let u1 : p2823 := h65715;
    (Or.elim h8013 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65717 (p4864 p5925 : Prop)
    (h65716 : p4864)
    (h12557 : (¬ p4864) ∨ p5925)
    : p5925 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5925) := (fun h => hn h);
    let u1 : p4864 := h65716;
    (Or.elim h12557 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65718 (p290 p296 p2389 : Prop)
    (h2912 : (¬ p290) ∨ p2389)
    (h2913 : (¬ p296) ∨ p2389)
    (h326 : p290 ∨ p296)
    : p2389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2389) := (fun h => hn h);
    let u1 : (¬ p290) := (Or.elim h2912 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p296) := (Or.elim h2913 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h326 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65719 (p2389 p2390 : Prop)
    (h65718 : p2389)
    (h2930 : (¬ p2389) ∨ p2390)
    : p2390 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2390) := (fun h => hn h);
    let u1 : p2389 := h65718;
    (Or.elim h2930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65720 (p2390 p4618 : Prop)
    (h65719 : p2390)
    (h7391 : (¬ p2390) ∨ p4618)
    : p4618 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4618) := (fun h => hn h);
    let u1 : p2390 := h65719;
    (Or.elim h7391 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65721 (p4618 p5844 : Prop)
    (h65720 : p4618)
    (h12079 : (¬ p4618) ∨ p5844)
    : p5844 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5844) := (fun h => hn h);
    let u1 : p4618 := h65720;
    (Or.elim h12079 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65722 (p170 p176 p2267 : Prop)
    (h2671 : (¬ p170) ∨ p2267)
    (h2672 : (¬ p176) ∨ p2267)
    (h196 : p170 ∨ p176)
    : p2267 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2267) := (fun h => hn h);
    let u1 : (¬ p170) := (Or.elim h2671 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p176) := (Or.elim h2672 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h196 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65723 (p2267 p2268 : Prop)
    (h65722 : p2267)
    (h2689 : (¬ p2267) ∨ p2268)
    : p2268 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2268) := (fun h => hn h);
    let u1 : p2267 := h65722;
    (Or.elim h2689 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65724 (p2268 p4553 : Prop)
    (h65723 : p2268)
    (h7215 : (¬ p2268) ∨ p4553)
    : p4553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4553) := (fun h => hn h);
    let u1 : p2268 := h65723;
    (Or.elim h7215 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65725 (p4553 p5817 : Prop)
    (h65724 : p4553)
    (h11920 : (¬ p4553) ∨ p5817)
    : p5817 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5817) := (fun h => hn h);
    let u1 : p4553 := h65724;
    (Or.elim h11920 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65726 (p2761 p3097 p3125 p3246 p4025 p4033 p4191 p4322 p4381 p4553 p4554 p4557 p4559 p4618 p4619 p4622 p4623 p5041 p5042 p5044 : Prop)
    (h65571 : p5041)
    (h65720 : p4618)
    (h65724 : p4553)
    (h10478 : (¬ p2761) ∨ (¬ p4381))
    (h6872 : (¬ p4033) ∨ (¬ p4191) ∨ p4322)
    (h23007 : (¬ p4191) ∨ p4381 ∨ (¬ p4623))
    (h8438 : p4033 ∨ (¬ p5042))
    (h7382 : (¬ p4622) ∨ p4623)
    (h8451 : (¬ p5041) ∨ p5042 ∨ p5044)
    (h7390 : (¬ p4618) ∨ p4619 ∨ p4622)
    (h8445 : p3125 ∨ (¬ p5044))
    (h7376 : p4025 ∨ (¬ p4619))
    (h20392 : (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4025))
    (h41086 : (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4559))
    (h7202 : p3097 ∨ (¬ p4554))
    (h7210 : (¬ p4557) ∨ p4559)
    (h7214 : (¬ p4553) ∨ p4554 ∨ p4557)
    : (¬ p4191) ∨ (¬ p2761) ∨ p4322 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4322) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5041 := h65571;
    let u5 : p4618 := h65720;
    let u6 : p4553 := h65724;
    let u7 : (¬ p4381) := (Or.elim h10478 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u8 : (¬ p4033) := (Or.elim h6872 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1))))));
    let u9 : (¬ p4623) := (Or.elim h23007 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => r1))));
    let u10 : (¬ p5042) := (Or.elim h8438 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4622) := (Or.elim h7382 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u12 : p5044 := (Or.elim h8451 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => r1))));
    let u13 : p4619 := (Or.elim h7390 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u11 r1))))));
    let u14 : p3125 := (Or.elim h8445 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u15 : p4025 := (Or.elim h7376 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u16 : (¬ p3097) := (Or.elim h20392 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (False.elim (r1 u15))))));
    let u17 : (¬ p4559) := (Or.elim h41086 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => r3))))))));
    let u18 : (¬ p4554) := (Or.elim h7202 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : (¬ p4557) := (Or.elim h7210 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    (Or.elim h7214 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u18 q1))) (fun r1 => (False.elim (u19 r1)))))))

theorem step65727 (p770 p776 p2894 : Prop)
    (h3914 : (¬ p770) ∨ p2894)
    (h3915 : (¬ p776) ∨ p2894)
    (h846 : p770 ∨ p776)
    : p2894 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2894) := (fun h => hn h);
    let u1 : (¬ p770) := (Or.elim h3914 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p776) := (Or.elim h3915 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h846 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65728 (p2894 p2895 : Prop)
    (h65727 : p2894)
    (h3932 : (¬ p2894) ∨ p2895)
    : p2895 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2895) := (fun h => hn h);
    let u1 : p2894 := h65727;
    (Or.elim h3932 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65729 (p2895 p4915 : Prop)
    (h65728 : p2895)
    (h8134 : (¬ p2895) ∨ p4915)
    : p4915 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4915) := (fun h => hn h);
    let u1 : p2895 := h65728;
    (Or.elim h8134 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65730 (p4915 p5946 : Prop)
    (h65729 : p4915)
    (h12679 : (¬ p4915) ∨ p5946)
    : p5946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5946) := (fun h => hn h);
    let u1 : p4915 := h65729;
    (Or.elim h12679 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65731 (p182 p188 p2277 : Prop)
    (h2691 : (¬ p182) ∨ p2277)
    (h2692 : (¬ p188) ∨ p2277)
    (h209 : p182 ∨ p188)
    : p2277 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2277) := (fun h => hn h);
    let u1 : (¬ p182) := (Or.elim h2691 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p188) := (Or.elim h2692 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h209 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65732 (p2277 p2278 : Prop)
    (h65731 : p2277)
    (h2709 : (¬ p2277) ∨ p2278)
    : p2278 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2278) := (fun h => hn h);
    let u1 : p2277 := h65731;
    (Or.elim h2709 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65733 (p2278 p4561 : Prop)
    (h65732 : p2278)
    (h7233 : (¬ p2278) ∨ p4561)
    : p4561 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4561) := (fun h => hn h);
    let u1 : p2278 := h65732;
    (Or.elim h7233 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65734 (p4561 p5820 : Prop)
    (h65733 : p4561)
    (h11937 : (¬ p4561) ∨ p5820)
    : p5820 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5820) := (fun h => hn h);
    let u1 : p4561 := h65733;
    (Or.elim h11937 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65735 (p50 p56 p2149 : Prop)
    (h2436 : (¬ p50) ∨ p2149)
    (h2437 : (¬ p56) ∨ p2149)
    (h66 : p50 ∨ p56)
    : p2149 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2149) := (fun h => hn h);
    let u1 : (¬ p50) := (Or.elim h2436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p56) := (Or.elim h2437 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h66 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65736 (p2149 p2150 : Prop)
    (h65735 : p2149)
    (h2454 : (¬ p2149) ∨ p2150)
    : p2150 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2150) := (fun h => hn h);
    let u1 : p2149 := h65735;
    (Or.elim h2454 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65737 (p2150 p4483 : Prop)
    (h65736 : p2150)
    (h7035 : (¬ p2150) ∨ p4483)
    : p4483 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4483) := (fun h => hn h);
    let u1 : p2150 := h65736;
    (Or.elim h7035 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65738 (p4483 p5790 : Prop)
    (h65737 : p4483)
    (h11764 : (¬ p4483) ∨ p5790)
    : p5790 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5790) := (fun h => hn h);
    let u1 : p4483 := h65737;
    (Or.elim h11764 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65739 (p722 p728 p2853 : Prop)
    (h3832 : (¬ p722) ∨ p2853)
    (h3833 : (¬ p728) ∨ p2853)
    (h794 : p722 ∨ p728)
    : p2853 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2853) := (fun h => hn h);
    let u1 : (¬ p722) := (Or.elim h3832 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p728) := (Or.elim h3833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h794 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65740 (p2853 p2854 : Prop)
    (h65739 : p2853)
    (h3850 : (¬ p2853) ∨ p2854)
    : p2854 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2854) := (fun h => hn h);
    let u1 : p2853 := h65739;
    (Or.elim h3850 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65741 (p2854 p4886 : Prop)
    (h65740 : p2854)
    (h8064 : (¬ p2854) ∨ p4886)
    : p4886 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4886) := (fun h => hn h);
    let u1 : p2854 := h65740;
    (Or.elim h8064 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65742 (p4886 p5934 : Prop)
    (h65741 : p4886)
    (h12608 : (¬ p4886) ∨ p5934)
    : p5934 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5934) := (fun h => hn h);
    let u1 : p4886 := h65741;
    (Or.elim h12608 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65745 (p2274 p3690 p3744 p3872 p4187 p4396 p4618 p4619 p4622 : Prop)
    (h65720 : p4618)
    (h33874 : p3690 ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p4396))
    (h19781 : (¬ p2274) ∨ (¬ p3744) ∨ (¬ p4187))
    (h7377 : p4396 ∨ (¬ p4619))
    (h7383 : p4187 ∨ (¬ p4622))
    (h7390 : (¬ p4618) ∨ p4619 ∨ p4622)
    : (¬ p3744) ∨ (¬ p2274) ∨ (¬ p3872) ∨ p3690 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3744 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3690) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4618 := h65720;
    let u5 : (¬ p4396) := (Or.elim h33874 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    let u6 : (¬ p4187) := (Or.elim h19781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u7 : (¬ p4619) := (Or.elim h7377 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u8 : (¬ p4622) := (Or.elim h7383 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    (Or.elim h7390 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (False.elim (u8 r1)))))))

theorem step65746 (p74 p80 p2170 : Prop)
    (h2478 : (¬ p74) ∨ p2170)
    (h2479 : (¬ p80) ∨ p2170)
    (h92 : p74 ∨ p80)
    : p2170 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2170) := (fun h => hn h);
    let u1 : (¬ p74) := (Or.elim h2478 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p80) := (Or.elim h2479 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h92 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65747 (p2170 p2171 : Prop)
    (h65746 : p2170)
    (h2496 : (¬ p2170) ∨ p2171)
    : p2171 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2171) := (fun h => hn h);
    let u1 : p2170 := h65746;
    (Or.elim h2496 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65748 (p2171 p4499 : Prop)
    (h65747 : p2171)
    (h7069 : (¬ p2171) ∨ p4499)
    : p4499 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4499) := (fun h => hn h);
    let u1 : p2171 := h65747;
    (Or.elim h7069 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65749 (p4499 p5796 : Prop)
    (h65748 : p4499)
    (h11798 : (¬ p4499) ∨ p5796)
    : p5796 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5796) := (fun h => hn h);
    let u1 : p4499 := h65748;
    (Or.elim h11798 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65751 (p2177 p2299 p3146 p3747 p4107 p4348 p4445 p4499 p4500 p4502 p4559 p4665 p4903 p4905 : Prop)
    (h65748 : p4499)
    (h8094 : (¬ p4903) ∨ p4905)
    (h8091 : p3747 ∨ (¬ p4903))
    (h7480 : p4445 ∨ (¬ p4665))
    (h7481 : p4348 ∨ (¬ p4665))
    (h41698 : (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4905))
    (h41325 : (¬ p2299) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4559))
    (h7062 : p2177 ∨ (¬ p4502))
    (h7056 : p2299 ∨ (¬ p4500))
    (h7068 : (¬ p4499) ∨ p4500 ∨ p4502)
    : (¬ p4665) ∨ (¬ p3146) ∨ (¬ p4903) ∨ (¬ p4107) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4665 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4903 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4499 := h65748;
    let u6 : p4905 := (Or.elim h8094 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u7 : p3747 := (Or.elim h8091 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : p4445 := (Or.elim h7480 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : p4348 := (Or.elim h7481 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : (¬ p2177) := (Or.elim h41698 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6))))))))));
    let u11 : (¬ p2299) := (Or.elim h41325 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u4))))))))));
    let u12 : (¬ p4502) := (Or.elim h7062 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4500) := (Or.elim h7056 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    (Or.elim h7068 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (False.elim (u12 r1)))))))

theorem step65752 (p206 p212 p2300 : Prop)
    (h2734 : (¬ p206) ∨ p2300)
    (h2735 : (¬ p212) ∨ p2300)
    (h235 : p206 ∨ p212)
    : p2300 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2300) := (fun h => hn h);
    let u1 : (¬ p206) := (Or.elim h2734 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p212) := (Or.elim h2735 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h235 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65753 (p2300 p2301 : Prop)
    (h65752 : p2300)
    (h2752 : (¬ p2300) ∨ p2301)
    : p2301 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2301) := (fun h => hn h);
    let u1 : p2300 := h65752;
    (Or.elim h2752 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65754 (p2301 p4573 : Prop)
    (h65753 : p2301)
    (h7255 : (¬ p2301) ∨ p4573)
    : p4573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4573) := (fun h => hn h);
    let u1 : p2301 := h65753;
    (Or.elim h7255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65756 (p254 p260 p2356 : Prop)
    (h2849 : (¬ p254) ∨ p2356)
    (h2850 : (¬ p260) ∨ p2356)
    (h287 : p254 ∨ p260)
    : p2356 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2356) := (fun h => hn h);
    let u1 : (¬ p254) := (Or.elim h2849 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p260) := (Or.elim h2850 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h287 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65757 (p2356 p2357 : Prop)
    (h65756 : p2356)
    (h2867 : (¬ p2356) ∨ p2357)
    : p2357 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2357) := (fun h => hn h);
    let u1 : p2356 := h65756;
    (Or.elim h2867 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65758 (p2357 p4599 : Prop)
    (h65757 : p2357)
    (h7339 : (¬ p2357) ∨ p4599)
    : p4599 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4599) := (fun h => hn h);
    let u1 : p2357 := h65757;
    (Or.elim h7339 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65759 (p4599 p5835 : Prop)
    (h65758 : p4599)
    (h12025 : (¬ p4599) ∨ p5835)
    : p5835 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5835) := (fun h => hn h);
    let u1 : p4599 := h65758;
    (Or.elim h12025 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65761 (p278 p284 p2376 : Prop)
    (h2889 : (¬ p278) ∨ p2376)
    (h2890 : (¬ p284) ∨ p2376)
    (h313 : p278 ∨ p284)
    : p2376 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2376) := (fun h => hn h);
    let u1 : (¬ p278) := (Or.elim h2889 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p284) := (Or.elim h2890 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h313 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65762 (p2376 p2377 : Prop)
    (h65761 : p2376)
    (h2907 : (¬ p2376) ∨ p2377)
    : p2377 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2377) := (fun h => hn h);
    let u1 : p2376 := h65761;
    (Or.elim h2907 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65763 (p2377 p4611 : Prop)
    (h65762 : p2377)
    (h7374 : (¬ p2377) ∨ p4611)
    : p4611 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4611) := (fun h => hn h);
    let u1 : p2377 := h65762;
    (Or.elim h7374 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65764 (p4611 p5841 : Prop)
    (h65763 : p4611)
    (h12061 : (¬ p4611) ∨ p5841)
    : p5841 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5841) := (fun h => hn h);
    let u1 : p4611 := h65763;
    (Or.elim h12061 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65765 (p230 p236 p2334 : Prop)
    (h2804 : (¬ p230) ∨ p2334)
    (h2805 : (¬ p236) ∨ p2334)
    (h261 : p230 ∨ p236)
    : p2334 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2334) := (fun h => hn h);
    let u1 : (¬ p230) := (Or.elim h2804 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p236) := (Or.elim h2805 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h261 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65766 (p2334 p2335 : Prop)
    (h65765 : p2334)
    (h2822 : (¬ p2334) ∨ p2335)
    : p2335 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2335) := (fun h => hn h);
    let u1 : p2334 := h65765;
    (Or.elim h2822 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65767 (p2335 p4585 : Prop)
    (h65766 : p2335)
    (h7305 : (¬ p2335) ∨ p4585)
    : p4585 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4585) := (fun h => hn h);
    let u1 : p2335 := h65766;
    (Or.elim h7305 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65768 (p4585 p5829 : Prop)
    (h65767 : p4585)
    (h11989 : (¬ p4585) ∨ p5829)
    : p5829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5829) := (fun h => hn h);
    let u1 : p4585 := h65767;
    (Or.elim h11989 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65769 (p266 p272 p2366 : Prop)
    (h2869 : (¬ p266) ∨ p2366)
    (h2870 : (¬ p272) ∨ p2366)
    (h300 : p266 ∨ p272)
    : p2366 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2366) := (fun h => hn h);
    let u1 : (¬ p266) := (Or.elim h2869 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p272) := (Or.elim h2870 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h300 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65770 (p2366 p2367 : Prop)
    (h65769 : p2366)
    (h2887 : (¬ p2366) ∨ p2367)
    : p2367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2367) := (fun h => hn h);
    let u1 : p2366 := h65769;
    (Or.elim h2887 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

end ElevenRUP
