import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step116181 (p3201 p3868 p4067 p4194 p4391 p4753 p6143 : Prop)
    (h105514 : p4753)
    (h54833 : (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4067) ∨ (¬ p4194) ∨ (¬ p4391) ∨ (¬ p4753))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3868) ∨ (¬ p4067) ∨ (¬ p4194) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4391) := (Or.elim h54833 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step116189 (p2264 p3146 p3256 p4391 p4431 p5648 p6143 : Prop)
    (h116097 : (¬ p5648) ∨ (¬ p2264) ∨ (¬ p4391) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p4431))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p5648) ∨ (¬ p2264) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5648 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4391) := (Or.elim h116097 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step116192 (p2241 p2573 p2996 p3461 p3564 p4391 p4831 p5190 p6143 : Prop)
    (h105487 : p5190)
    (h105445 : p4831)
    (h80785 : (¬ p4391) ∨ p2241 ∨ (¬ p5190) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p2996) ∨ (¬ p3564) ∨ (¬ p4831))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3461) ∨ (¬ p2996) ∨ (¬ p3564) ∨ p2241 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5190 := h105487;
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h80785 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116194 (p2156 p2241 p2996 p3125 p3461 p4391 p4521 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h80787 : (¬ p3461) ∨ p2241 ∨ (¬ p4521) ∨ (¬ p4831) ∨ (¬ p4391) ∨ (¬ p2996) ∨ (¬ p2156) ∨ (¬ p3125))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3461) ∨ (¬ p2996) ∨ p2241 ∨ (¬ p3125) ∨ (¬ p2156) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h80787 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u4))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116195 (p2230 p2685 p2696 p2982 p3680 p4391 p4419 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h82590 : (¬ p4391) ∨ (¬ p2982) ∨ (¬ p3680) ∨ p2685 ∨ (¬ p4419) ∨ p2696 ∨ (¬ p2230) ∨ (¬ p4831))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3680) ∨ (¬ p2230) ∨ p2685 ∨ p2696 ∨ (¬ p2982) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h82590 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116196 (p2139 p2156 p2685 p2696 p3125 p3461 p4391 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h82591 : (¬ p4391) ∨ p2685 ∨ (¬ p3461) ∨ p2696 ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p4831))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3461) ∨ (¬ p2156) ∨ p2696 ∨ p2685 ∨ (¬ p3125) ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h82591 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116197 (p2470 p2528 p2685 p2696 p3266 p4391 p4419 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h82592 : (¬ p4391) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p4419) ∨ p2696 ∨ p2685 ∨ (¬ p4831) ∨ (¬ p3266))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3266) ∨ p2685 ∨ (¬ p4419) ∨ (¬ p2528) ∨ (¬ p2470) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h82592 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116198 (p2573 p2685 p2696 p3461 p3564 p4391 p4419 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h82730 : (¬ p4391) ∨ (¬ p4831) ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p4419) ∨ p2696 ∨ (¬ p3461) ∨ p2685)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3461) ∨ (¬ p2573) ∨ (¬ p3564) ∨ p2685 ∨ p2696 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h82730 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116199 (p2685 p2696 p3093 p3319 p3461 p4391 p4736 p4831 p6143 : Prop)
    (h105431 : p4736)
    (h105445 : p4831)
    (h84208 : (¬ p3461) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4736) ∨ p2696 ∨ p2685)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3461) ∨ (¬ p3093) ∨ p2685 ∨ p2696 ∨ (¬ p3319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h84208 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (u3 r6))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116200 (p2230 p2241 p2982 p2996 p3680 p4391 p4831 p5190 p6143 : Prop)
    (h105487 : p5190)
    (h105445 : p4831)
    (h95382 : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p5190) ∨ (¬ p2996) ∨ (¬ p4831) ∨ p2241)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3680) ∨ (¬ p2230) ∨ (¬ p2996) ∨ p2241 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5190 := h105487;
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h95382 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116202 (p2396 p2651 p2685 p3276 p3343 p3791 p4391 p4790 p6143 : Prop)
    (h106424 : p4790)
    (h98785 : (¬ p3791) ∨ (¬ p4391) ∨ p2396 ∨ p2685 ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p3343) ∨ (¬ p4790))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3791) ∨ p2685 ∨ (¬ p3276) ∨ (¬ p2651) ∨ p2396 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4790 := h106424;
    let u8 : (¬ p4391) := (Or.elim h98785 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116203 (p2177 p2210 p2254 p2807 p2972 p3680 p3791 p4391 p6143 : Prop)
    (h105366 : p2254)
    (h98792 : (¬ p4391) ∨ (¬ p3680) ∨ (¬ p2254) ∨ (¬ p2972) ∨ p2807 ∨ (¬ p3791) ∨ p2177 ∨ (¬ p2210))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3791) ∨ p2807 ∨ (¬ p2972) ∨ (¬ p3680) ∨ p2177 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : (¬ p4391) := (Or.elim h98792 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116204 (p2139 p2220 p2685 p2696 p3146 p3266 p4391 p4831 p6143 : Prop)
    (h105445 : p4831)
    (h99592 : (¬ p4391) ∨ p2685 ∨ (¬ p2220) ∨ (¬ p4831) ∨ p2696 ∨ (¬ p2139) ∨ (¬ p3146) ∨ (¬ p3266))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p2696 ∨ (¬ p3266) ∨ p2685 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4831 := h105445;
    let u8 : (¬ p4391) := (Or.elim h99592 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u4))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116206 (p2220 p2437 p3016 p3146 p3266 p3399 p4391 p5648 p6143 : Prop)
    (h116113 : (¬ p5648) ∨ p2437 ∨ p2220 ∨ p3146 ∨ (¬ p3016) ∨ (¬ p3399) ∨ p3266 ∨ (¬ p4391))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p5648) ∨ p2437 ∨ p2220 ∨ p3146 ∨ (¬ p3016) ∨ (¬ p3399) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5648 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4391) := (Or.elim h116113 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step116207 (p2573 p2630 p2807 p3461 p3564 p4236 p4253 p4391 p4781 p6143 : Prop)
    (h107641 : (¬ p4391) ∨ (¬ p4253) ∨ (¬ p4236) ∨ (¬ p4781) ∨ (¬ p3461) ∨ p2630 ∨ (¬ p3564) ∨ (¬ p2573) ∨ p2807)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p3564) ∨ (¬ p3461) ∨ p2630 ∨ p2807 ∨ (¬ p2573) ∨ (¬ p4236) ∨ (¬ p4253) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4391) := (Or.elim h107641 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u9 r0)))))

theorem step116213 (p2241 p2598 p2750 p2753 p2911 p3032 p3201 p3399 p4391 p5559 p6143 : Prop)
    (h106345 : p2750)
    (h106189 : p5559)
    (h97611 : p3399 ∨ (¬ p3032) ∨ (¬ p2753) ∨ (¬ p4391) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3201) ∨ (¬ p5559))
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ (¬ p2911) ∨ (¬ p2598) ∨ (¬ p3032) ∨ (¬ p3201) ∨ (¬ p2753) ∨ p3399 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p5559 := h106189;
    let u10 : (¬ p4391) := (Or.elim h97611 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u10 r0)))))

theorem step116222 (p2220 p2331 p2373 p2396 p2563 p3366 p3519 p3791 p4067 p4236 p4376 p4391 p4399 p6143 : Prop)
    (h106320 : p4376)
    (h78931 : (¬ p3791) ∨ (¬ p4399) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p2563) ∨ (¬ p2220) ∨ (¬ p4391) ∨ (¬ p3519) ∨ (¬ p4067) ∨ p2396 ∨ p2373 ∨ (¬ p4376) ∨ p2331)
    (h116152 : (¬ p6143) ∨ p4391)
    : (¬ p6143) ∨ p2396 ∨ (¬ p2220) ∨ p2331 ∨ (¬ p2563) ∨ p2373 ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p3791) ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4376 := h106320;
    let u13 : (¬ p4391) := (Or.elim h78931 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u5 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (False.elim (u3 r11))))))))))))))))))))))))));
    (Or.elim h116152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u13 r0)))))

theorem step116223 (p4181 p5696 p6182 : Prop)
    (h109094 : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p4181))
    (h10230 : p4181 ∨ (¬ p5696))
    : (¬ p5696) ∨ (¬ p6182) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4181) := (Or.elim h109094 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h10230 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116224 (p4181 p5696 p6182 : Prop)
    (h109095 : p6182 ∨ p5696 ∨ (¬ p4181))
    (h15268 : p4181 ∨ p6182)
    : p6182 ∨ p5696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6182) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4181) := (Or.elim h109095 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h15268 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116225 (p4181 p5696 p6182 : Prop)
    (h116223 : (¬ p5696) ∨ (¬ p6182))
    (h15268 : p4181 ∨ p6182)
    : p4181 ∨ (¬ p5696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4181) := (fun h => hn (Or.inl h));
    let u1 : p5696 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6182) := (Or.elim h116223 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h15268 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116226 (p5693 p5696 p6182 : Prop)
    (h108592 : p5693 ∨ (¬ p6182))
    (h116224 : p6182 ∨ p5696)
    : p5696 ∨ p5693 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5693) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6182) := (Or.elim h108592 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116224 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116229 (p4181 p5693 p5696 : Prop)
    (h116225 : p4181 ∨ (¬ p5696))
    (h116226 : p5696 ∨ p5693)
    : p5693 ∨ p4181 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5693) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4181) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5696) := (Or.elim h116225 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116226 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116233 (p4019 p5615 p6161 : Prop)
    (h108548 : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161))
    (h9887 : p4019 ∨ (¬ p5615))
    : (¬ p5615) ∨ (¬ p6161) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6161 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4019) := (Or.elim h108548 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9887 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116234 (p4019 p5615 p6161 : Prop)
    (h108549 : p6161 ∨ (¬ p4019) ∨ p5615)
    (h14544 : p4019 ∨ p6161)
    : p6161 ∨ p5615 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5615) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4019) := (Or.elim h108549 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14544 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116236 (p5612 p5615 p6161 : Prop)
    (h116233 : (¬ p5615) ∨ (¬ p6161))
    (h108544 : p5615 ∨ p5612)
    : p5612 ∨ (¬ p6161) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5612) := (fun h => hn (Or.inl h));
    let u1 : p6161 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5615) := (Or.elim h116233 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108544 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116237 (p4019 p5615 p6161 : Prop)
    (h9887 : p4019 ∨ (¬ p5615))
    (h116234 : p6161 ∨ p5615)
    : p6161 ∨ p4019 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4019) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5615) := (Or.elim h9887 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116234 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116238 (p2098 p2598 p3641 p4149 p5615 p6161 : Prop)
    (h110725 : p3641 ∨ (¬ p5615) ∨ p4149 ∨ (¬ p2598) ∨ p2098)
    (h116234 : p6161 ∨ p5615)
    : p6161 ∨ p3641 ∨ p4149 ∨ (¬ p2598) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5615) := (Or.elim h110725 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116234 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116240 (p4019 p5612 p6161 : Prop)
    (h116236 : p5612 ∨ (¬ p6161))
    (h116237 : p6161 ∨ p4019)
    : p4019 ∨ p5612 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4019) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5612) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6161) := (Or.elim h116236 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116237 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116242 (p2098 p2598 p3641 p4149 p5612 p6161 : Prop)
    (h116238 : p6161 ∨ p3641 ∨ p4149 ∨ (¬ p2598) ∨ p2098)
    (h116236 : p5612 ∨ (¬ p6161))
    : p5612 ∨ p3641 ∨ p4149 ∨ (¬ p2598) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5612) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p6161 := (Or.elim h116238 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116236 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step116245 (p5597 p5600 p6157 : Prop)
    (h109631 : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157))
    (h9864 : (¬ p5597) ∨ p5600)
    : (¬ p5597) ∨ (¬ p6157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5597 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6157 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5600) := (Or.elim h109631 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9864 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116246 (p5597 p5600 p6157 : Prop)
    (h109632 : p6157 ∨ (¬ p5600) ∨ p5597)
    (h14520 : p5600 ∨ p6157)
    : p6157 ∨ p5597 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5597) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5600) := (Or.elim h109632 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14520 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116247 (p4009 p5597 p6157 : Prop)
    (h116245 : (¬ p5597) ∨ (¬ p6157))
    (h108534 : p5597 ∨ p4009)
    : p4009 ∨ (¬ p6157) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4009) := (fun h => hn (Or.inl h));
    let u1 : p6157 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5597) := (Or.elim h116245 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108534 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116249 (p5597 p5600 p6157 : Prop)
    (h9864 : (¬ p5597) ∨ p5600)
    (h116246 : p6157 ∨ p5597)
    : p6157 ∨ p5600 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5600) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5597) := (Or.elim h9864 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h116246 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116263 (p3868 p5506 p6131 : Prop)
    (h109059 : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131))
    (h9589 : p3868 ∨ (¬ p5506))
    : (¬ p5506) ∨ (¬ p6131) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6131 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3868) := (Or.elim h109059 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9589 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116264 (p3868 p5506 p6131 : Prop)
    (h109060 : p6131 ∨ (¬ p3868) ∨ p5506)
    (h14040 : p3868 ∨ p6131)
    : p6131 ∨ p5506 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5506) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3868) := (Or.elim h109060 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14040 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116265 (p5500 p5506 p6131 : Prop)
    (h116263 : (¬ p5506) ∨ (¬ p6131))
    (h66479 : p5500 ∨ p5506)
    : p5500 ∨ (¬ p6131) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5500) := (fun h => hn (Or.inl h));
    let u1 : p6131 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5506) := (Or.elim h116263 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h66479 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116266 (p3868 p5506 p6131 : Prop)
    (h9589 : p3868 ∨ (¬ p5506))
    (h116264 : p6131 ∨ p5506)
    : p6131 ∨ p3868 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3868) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5506) := (Or.elim h9589 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h116264 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116267 (p2177 p2493 p3801 p4260 p5506 p6131 : Prop)
    (h108756 : (¬ p5506) ∨ (¬ p3801) ∨ (¬ p4260) ∨ (¬ p2177) ∨ p2493)
    (h116264 : p6131 ∨ p5506)
    : p6131 ∨ (¬ p3801) ∨ (¬ p4260) ∨ (¬ p2177) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : p3801 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5506) := (Or.elim h108756 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116264 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step116274 (p2177 p2241 p2717 p2753 p3189 p3425 p3449 p4149 p5506 p5600 p6131 : Prop)
    (h112173 : p3189 ∨ (¬ p5506) ∨ (¬ p4149) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ p2177)
    (h116264 : p6131 ∨ p5506)
    : p6131 ∨ p3189 ∨ (¬ p4149) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5506) := (Or.elim h112173 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h116264 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step116278 (p5500 p5503 p6130 : Prop)
    (h109360 : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130))
    (h9583 : (¬ p5500) ∨ p5503)
    : (¬ p5500) ∨ (¬ p6130) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6130 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5503) := (Or.elim h109360 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9583 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116279 (p5500 p5503 p6130 : Prop)
    (h109362 : p6130 ∨ (¬ p5503) ∨ p5500)
    (h14033 : p5503 ∨ p6130)
    : p6130 ∨ p5500 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5500) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5503) := (Or.elim h109362 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h14033 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116295 (p3212 p5092 p6008 : Prop)
    (h112509 : (¬ p5092) ∨ (¬ p6008) ∨ (¬ p3212))
    (h8577 : p3212 ∨ (¬ p5092))
    : (¬ p5092) ∨ (¬ p6008) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6008 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3212) := (Or.elim h112509 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h8577 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116296 (p2509 p4683 p5866 : Prop)
    (h114514 : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p2509))
    (h7550 : p2509 ∨ (¬ p4683))
    : (¬ p4683) ∨ (¬ p5866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4683 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2509) := (Or.elim h114514 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h7550 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116298 (p2630 p2737 p2797 p3367 : Prop)
    (h103020 : p2737 ∨ p2797 ∨ (¬ p3367) ∨ (¬ p2630))
    (h114039 : p2630 ∨ p2737 ∨ (¬ p3367))
    : p2797 ∨ (¬ p3367) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2630) := (Or.elim h103020 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h114039 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116299 (p2563 p2829 p2839 p2860 : Prop)
    (h107231 : p2829 ∨ (¬ p2839) ∨ p2860 ∨ (¬ p2563))
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : (¬ p2839) ∨ p2829 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h107231 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116301 (p2187 p2352 p2363 p3146 : Prop)
    (h107251 : p3146 ∨ (¬ p2363) ∨ (¬ p2352) ∨ p2187)
    (h114372 : (¬ p2187) ∨ p3146 ∨ (¬ p2363))
    : (¬ p2352) ∨ p3146 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2187 := (Or.elim h107251 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => r2))))));
    (Or.elim h114372 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116304 (p2761 p3461 p3516 p4063 : Prop)
    (h108644 : (¬ p2761) ∨ p3461 ∨ (¬ p4063) ∨ p3516)
    (h108388 : p2761 ∨ (¬ p4063) ∨ p3516)
    : p3461 ∨ (¬ p4063) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2761) := (Or.elim h108644 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h108388 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116305 (p2459 p3266 p3461 p5558 : Prop)
    (h108987 : p3266 ∨ (¬ p3461) ∨ (¬ p5558) ∨ (¬ p2459))
    (h109250 : (¬ p3266) ∨ (¬ p5558) ∨ (¬ p2459))
    : (¬ p3461) ∨ (¬ p5558) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3266 := (Or.elim h108987 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109250 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116307 (p3193 p3276 p3707 p5160 : Prop)
    (h109386 : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p5160))
    (h110334 : (¬ p3193) ∨ p3276 ∨ (¬ p3707))
    : p3276 ∨ (¬ p3707) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3193 := (Or.elim h109386 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110334 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116309 (p2341 p2761 p3516 p3773 : Prop)
    (h109445 : p3516 ∨ (¬ p3773) ∨ (¬ p2341) ∨ (¬ p2761))
    (h109544 : (¬ p3516) ∨ (¬ p2761) ∨ (¬ p3773))
    : (¬ p3773) ∨ (¬ p2341) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3773 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3516 := (Or.elim h109445 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109544 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116311 (p2972 p3115 p3707 p4322 : Prop)
    (h109562 : (¬ p2972) ∨ (¬ p3707) ∨ p3115 ∨ (¬ p4322))
    (h110190 : p2972 ∨ (¬ p3707) ∨ (¬ p4322))
    : (¬ p3707) ∨ p3115 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2972) := (Or.elim h109562 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116312 (p2192 p2972 p3707 p4322 : Prop)
    (h109563 : (¬ p2972) ∨ (¬ p3707) ∨ p2192 ∨ (¬ p4322))
    (h110190 : p2972 ∨ (¬ p3707) ∨ (¬ p4322))
    : (¬ p3707) ∨ p2192 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2972) := (Or.elim h109563 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116313 (p2972 p3105 p3707 p4322 : Prop)
    (h109564 : (¬ p2972) ∨ (¬ p3707) ∨ (¬ p4322) ∨ p3105)
    (h110190 : p2972 ∨ (¬ p3707) ∨ (¬ p4322))
    : (¬ p3707) ∨ (¬ p4322) ∨ p3105 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2972) := (Or.elim h109564 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110190 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116314 (p3146 p3266 p3461 p3969 : Prop)
    (h109662 : (¬ p3266) ∨ p3461 ∨ (¬ p3969) ∨ p3146)
    (h109591 : p3266 ∨ (¬ p3969) ∨ p3146)
    : p3461 ∨ (¬ p3969) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3266) := (Or.elim h109662 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h109591 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116315 (p2717 p2761 p3434 p3670 : Prop)
    (h109674 : (¬ p3434) ∨ p2761 ∨ (¬ p3670) ∨ p2717)
    (h109278 : p3434 ∨ p2761 ∨ (¬ p3670))
    : p2761 ∨ (¬ p3670) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3434) := (Or.elim h109674 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h109278 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116316 (p2396 p2761 p3631 p3707 : Prop)
    (h109860 : p3631 ∨ p3707 ∨ (¬ p2396) ∨ (¬ p2761))
    (h110058 : (¬ p3631) ∨ (¬ p2761) ∨ p3707)
    : p3707 ∨ (¬ p2396) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h109860 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110058 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116317 (p2761 p3527 p3631 p3707 : Prop)
    (h109864 : p3631 ∨ (¬ p2761) ∨ p3707 ∨ (¬ p3527))
    (h110058 : (¬ p3631) ∨ (¬ p2761) ∨ p3707)
    : (¬ p2761) ∨ p3707 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h109864 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110058 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116318 (p2707 p2717 p3434 p3537 : Prop)
    (h109923 : p2717 ∨ (¬ p3434) ∨ (¬ p2707) ∨ p3537)
    (h110684 : (¬ p2717) ∨ (¬ p2707) ∨ p3537)
    : (¬ p3434) ∨ (¬ p2707) ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2717 := (Or.elim h109923 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110684 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116319 (p2440 p3276 p3343 p5284 : Prop)
    (h109940 : p3343 ∨ (¬ p5284) ∨ (¬ p3276) ∨ p2440)
    (h111255 : (¬ p3343) ∨ (¬ p3276) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3276) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3343 := (Or.elim h109940 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111255 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116320 (p3073 p3449 p3830 p4181 : Prop)
    (h110126 : p3073 ∨ (¬ p4181) ∨ (¬ p3449) ∨ p3830)
    (h110470 : (¬ p3073) ∨ (¬ p3449) ∨ p3830)
    : (¬ p4181) ∨ (¬ p3449) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3073 := (Or.elim h110126 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110470 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116321 (p3073 p3146 p3449 p3830 : Prop)
    (h110129 : p3073 ∨ (¬ p3449) ∨ p3830 ∨ (¬ p3146))
    (h110470 : (¬ p3073) ∨ (¬ p3449) ∨ p3830)
    : (¬ p3449) ∨ p3830 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3073 := (Or.elim h110129 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110470 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116322 (p2210 p2972 p2982 p3830 : Prop)
    (h110192 : p2972 ∨ p3830 ∨ (¬ p2982) ∨ (¬ p2210))
    (h109715 : (¬ p2972) ∨ p3830 ∨ (¬ p2210))
    : p3830 ∨ (¬ p2982) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2972 := (Or.elim h110192 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109715 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116323 (p2192 p2210 p2972 p3830 : Prop)
    (h110197 : p2972 ∨ (¬ p2192) ∨ p3830 ∨ (¬ p2210))
    (h109715 : (¬ p2972) ∨ p3830 ∨ (¬ p2210))
    : (¬ p2192) ∨ p3830 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2972 := (Or.elim h110197 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109715 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116324 (p3093 p3319 p3483 p3830 : Prop)
    (h110315 : p3319 ∨ p3830 ∨ (¬ p3483) ∨ (¬ p3093))
    (h109714 : (¬ p3319) ∨ p3830 ∨ (¬ p3093))
    : p3830 ∨ (¬ p3483) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3319 := (Or.elim h110315 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109714 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116326 (p3193 p3343 p3379 p3830 : Prop)
    (h110337 : (¬ p3193) ∨ p3830 ∨ (¬ p3379) ∨ (¬ p3343))
    (h109384 : p3193 ∨ p3830 ∨ (¬ p3379))
    : p3830 ∨ (¬ p3379) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3193) := (Or.elim h110337 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109384 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116327 (p3193 p3333 p3379 p3830 : Prop)
    (h110339 : (¬ p3193) ∨ p3830 ∨ (¬ p3379) ∨ (¬ p3333))
    (h109384 : p3193 ∨ p3830 ∨ (¬ p3379))
    : p3830 ∨ (¬ p3379) ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3193) := (Or.elim h110339 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109384 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116329 (p3193 p3379 p3830 p5160 : Prop)
    (h110423 : p3193 ∨ (¬ p3830) ∨ (¬ p5160) ∨ p3379)
    (h107089 : (¬ p3830) ∨ p3379 ∨ (¬ p3193))
    : (¬ p3830) ∨ (¬ p5160) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3193 := (Or.elim h110423 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h107089 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116330 (p2098 p2187 p2774 p2819 : Prop)
    (h110444 : (¬ p2819) ∨ (¬ p2098) ∨ p2774 ∨ p2187)
    (h111540 : p2819 ∨ (¬ p2098) ∨ p2774)
    : (¬ p2098) ∨ p2774 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2819) := (Or.elim h110444 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111540 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116331 (p2098 p2352 p2774 p2819 : Prop)
    (h110447 : (¬ p2819) ∨ (¬ p2098) ∨ p2774 ∨ p2352)
    (h111540 : p2819 ∨ (¬ p2098) ∨ p2774)
    : (¬ p2098) ∨ p2774 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2819) := (Or.elim h110447 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111540 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116332 (p2122 p2819 p2829 p3537 : Prop)
    (h110449 : (¬ p2819) ∨ (¬ p3537) ∨ p2829 ∨ p2122)
    (h111541 : p2819 ∨ (¬ p3537) ∨ p2829)
    : (¬ p3537) ∨ p2829 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2819) := (Or.elim h110449 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111541 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116333 (p3246 p3399 p3631 p3830 : Prop)
    (h110520 : p3631 ∨ (¬ p3246) ∨ p3830 ∨ (¬ p3399))
    (h110600 : (¬ p3631) ∨ p3830 ∨ (¬ p3399))
    : (¬ p3246) ∨ p3830 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h110520 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110600 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116334 (p2396 p3399 p3631 p3830 : Prop)
    (h110521 : p3631 ∨ (¬ p2396) ∨ p3830 ∨ (¬ p3399))
    (h110600 : (¬ p3631) ∨ p3830 ∨ (¬ p3399))
    : (¬ p2396) ∨ p3830 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h110521 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110600 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116335 (p3399 p3527 p3631 p3830 : Prop)
    (h110523 : p3631 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p3830)
    (h110600 : (¬ p3631) ∨ p3830 ∨ (¬ p3399))
    : (¬ p3527) ∨ (¬ p3399) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h110523 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110600 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116336 (p2417 p3399 p3631 p3830 : Prop)
    (h110524 : p3631 ∨ (¬ p2417) ∨ (¬ p3399) ∨ p3830)
    (h110600 : (¬ p3631) ∨ p3830 ∨ (¬ p3399))
    : (¬ p2417) ∨ (¬ p3399) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3631 := (Or.elim h110524 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110600 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116337 (p2417 p2449 p2807 p3286 : Prop)
    (h110656 : (¬ p2449) ∨ (¬ p3286) ∨ p2417 ∨ p2807)
    (h110899 : p2449 ∨ (¬ p3286) ∨ p2807)
    : (¬ p3286) ∨ p2417 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2449) := (Or.elim h110656 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110899 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116338 (p2449 p2685 p3246 p3755 : Prop)
    (h110660 : (¬ p2449) ∨ (¬ p3755) ∨ p2685 ∨ p3246)
    (h110901 : p2449 ∨ (¬ p3755) ∨ p2685)
    : (¬ p3755) ∨ p2685 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2449) := (Or.elim h110660 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110901 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116339 (p2396 p2449 p2685 p3755 : Prop)
    (h110661 : (¬ p2449) ∨ (¬ p3755) ∨ p2685 ∨ p2396)
    (h110901 : p2449 ∨ (¬ p3755) ∨ p2685)
    : (¬ p3755) ∨ p2685 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2449) := (Or.elim h110661 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110901 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116340 (p2470 p3367 p3537 p3641 : Prop)
    (h110714 : p3641 ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2470))
    (h110392 : (¬ p3641) ∨ p3537 ∨ (¬ p3367))
    : p3537 ∨ (¬ p3367) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3641 := (Or.elim h110714 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110392 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116341 (p2850 p3367 p3537 p3641 : Prop)
    (h110715 : p3641 ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2850))
    (h110392 : (¬ p3641) ∨ p3537 ∨ (¬ p3367))
    : p3537 ∨ (¬ p3367) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3641 := (Or.elim h110715 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110392 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116343 (p3083 p3367 p3537 p3641 : Prop)
    (h110721 : p3641 ∨ p3537 ∨ (¬ p3083) ∨ (¬ p3367))
    (h110392 : (¬ p3641) ∨ p3537 ∨ (¬ p3367))
    : p3537 ∨ (¬ p3083) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3641 := (Or.elim h110721 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110392 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116344 (p2946 p3105 p3115 p3286 : Prop)
    (h110851 : (¬ p3115) ∨ p3105 ∨ (¬ p3286) ∨ p2946)
    (h109503 : p3115 ∨ (¬ p3286) ∨ p2946)
    : p3105 ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3115) := (Or.elim h110851 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h109503 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116345 (p2284 p2946 p3115 p3286 : Prop)
    (h110852 : (¬ p3115) ∨ p2284 ∨ (¬ p3286) ∨ p2946)
    (h109503 : p3115 ∨ (¬ p3286) ∨ p2946)
    : p2284 ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3115) := (Or.elim h110852 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h109503 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116346 (p2797 p3323 p3755 p4228 : Prop)
    (h110874 : (¬ p3323) ∨ p4228 ∨ (¬ p3755) ∨ p2797)
    (h110991 : p3323 ∨ (¬ p3755) ∨ p2797)
    : p4228 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3323) := (Or.elim h110874 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110991 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116347 (p2295 p2797 p3323 p3755 : Prop)
    (h110879 : (¬ p3323) ∨ (¬ p3755) ∨ p2295 ∨ p2797)
    (h110991 : p3323 ∨ (¬ p3755) ∨ p2797)
    : (¬ p3755) ∨ p2295 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3323) := (Or.elim h110879 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110991 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116348 (p2797 p3323 p3654 p3755 : Prop)
    (h110880 : (¬ p3323) ∨ (¬ p3755) ∨ p3654 ∨ p2797)
    (h110991 : p3323 ∨ (¬ p3755) ∨ p2797)
    : (¬ p3755) ∨ p3654 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3323) := (Or.elim h110880 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110991 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116349 (p2331 p3286 p3323 p3917 : Prop)
    (h110884 : (¬ p3323) ∨ (¬ p3917) ∨ (¬ p3286) ∨ p2331)
    (h110992 : p3323 ∨ (¬ p3286) ∨ p2331)
    : (¬ p3917) ∨ (¬ p3286) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3323) := (Or.elim h110884 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h110992 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116351 (p3125 p3323 p3461 p5284 : Prop)
    (h111001 : p3323 ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p5284))
    (h110870 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p5284))
    : (¬ p3125) ∨ (¬ p3461) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3323 := (Or.elim h111001 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110870 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116352 (p3399 p3449 p3527 p4442 : Prop)
    (h111028 : (¬ p3527) ∨ (¬ p4442) ∨ p3399 ∨ (¬ p3449))
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p4442) ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3527) := (Or.elim h111028 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116353 (p3399 p3449 p3527 p3631 : Prop)
    (h111030 : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p3631)
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p3449) ∨ p3399 ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3527) := (Or.elim h111030 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116354 (p2098 p2509 p2598 p3641 : Prop)
    (h111128 : (¬ p3641) ∨ (¬ p2098) ∨ (¬ p2509) ∨ p2598)
    (h111465 : p3641 ∨ (¬ p2098) ∨ p2598)
    : (¬ p2098) ∨ (¬ p2509) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3641) := (Or.elim h111128 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111465 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116355 (p2440 p2563 p2982 p3343 : Prop)
    (h111226 : p2982 ∨ p3343 ∨ p2440 ∨ (¬ p2563))
    (h109996 : (¬ p2982) ∨ p3343 ∨ p2440)
    : p3343 ∨ p2440 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2982 := (Or.elim h111226 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109996 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116356 (p2230 p2982 p3115 p3346 : Prop)
    (h111230 : p2982 ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p2230))
    (h109994 : (¬ p2982) ∨ (¬ p3346) ∨ (¬ p2230))
    : (¬ p3115) ∨ (¬ p3346) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2982 := (Or.elim h111230 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h109994 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116357 (p2122 p2396 p2819 p3434 : Prop)
    (h111323 : (¬ p2122) ∨ (¬ p3434) ∨ p2819 ∨ p2396)
    (h111732 : p2122 ∨ (¬ p3434) ∨ p2396)
    : (¬ p3434) ∨ p2819 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2122) := (Or.elim h111323 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111732 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116359 (p2417 p2850 p3201 p3434 : Prop)
    (h111399 : p3201 ∨ (¬ p2417) ∨ p3434 ∨ (¬ p2850))
    (h113431 : (¬ p3201) ∨ (¬ p2417) ∨ p3434)
    : (¬ p2417) ∨ p3434 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3201 := (Or.elim h111399 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113431 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116360 (p2437 p2717 p2911 p3201 : Prop)
    (h111400 : p3201 ∨ p2717 ∨ (¬ p2911) ∨ (¬ p2437))
    (h113432 : (¬ p3201) ∨ p2717 ∨ (¬ p2911))
    : p2717 ∨ (¬ p2911) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3201 := (Or.elim h111400 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113432 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116361 (p2417 p2437 p3201 p3434 : Prop)
    (h111401 : p3201 ∨ p3434 ∨ (¬ p2437) ∨ (¬ p2417))
    (h113431 : (¬ p3201) ∨ (¬ p2417) ∨ p3434)
    : p3434 ∨ (¬ p2437) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3201 := (Or.elim h111401 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113431 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116362 (p2274 p3125 p3461 p3680 : Prop)
    (h111441 : (¬ p3125) ∨ p2274 ∨ (¬ p3680) ∨ p3461)
    (h112415 : p3125 ∨ p3461 ∨ (¬ p3680))
    : p2274 ∨ (¬ p3680) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3125) := (Or.elim h111441 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112415 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116363 (p3125 p3461 p3564 p3680 : Prop)
    (h111442 : (¬ p3125) ∨ p3461 ∨ (¬ p3680) ∨ p3564)
    (h112415 : p3125 ∨ p3461 ∨ (¬ p3680))
    : p3461 ∨ (¬ p3680) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3125) := (Or.elim h111442 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112415 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116364 (p2470 p2528 p3609 p3641 : Prop)
    (h111468 : p3641 ∨ (¬ p2470) ∨ (¬ p2528) ∨ p3609)
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p2470) ∨ (¬ p2528) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3641 := (Or.elim h111468 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116366 (p2363 p2383 p2819 p3609 : Prop)
    (h111543 : p2819 ∨ (¬ p2383) ∨ p3609 ∨ (¬ p2363))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : (¬ p2383) ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2819 := (Or.elim h111543 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116367 (p2459 p2528 p3083 p3343 : Prop)
    (h111580 : (¬ p2528) ∨ p2459 ∨ p3083 ∨ (¬ p3343))
    (h112462 : p2528 ∨ p3083 ∨ (¬ p3343))
    : p2459 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111580 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112462 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116368 (p2528 p3083 p3343 p4149 : Prop)
    (h111581 : (¬ p2528) ∨ p4149 ∨ p3083 ∨ (¬ p3343))
    (h112462 : p2528 ∨ p3083 ∨ (¬ p3343))
    : p4149 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111581 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112462 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116369 (p2363 p2470 p2528 p3355 : Prop)
    (h111583 : (¬ p2528) ∨ p2363 ∨ p2470 ∨ (¬ p3355))
    (h112466 : p2528 ∨ p2470 ∨ (¬ p3355))
    : p2363 ∨ p2470 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111583 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112466 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116370 (p2470 p2528 p3146 p3355 : Prop)
    (h111584 : (¬ p2528) ∨ p3146 ∨ (¬ p3355) ∨ p2470)
    (h112466 : p2528 ∨ p2470 ∨ (¬ p3355))
    : p3146 ∨ (¬ p3355) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111584 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112466 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116371 (p2528 p3333 p3641 p4149 : Prop)
    (h111587 : (¬ p2528) ∨ p4149 ∨ p3641 ∨ (¬ p3333))
    (h112468 : p2528 ∨ (¬ p3333) ∨ p3641)
    : p4149 ∨ p3641 ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111587 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112468 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116372 (p2528 p3083 p3146 p3343 : Prop)
    (h111590 : (¬ p2528) ∨ p3146 ∨ p3083 ∨ (¬ p3343))
    (h112462 : p2528 ∨ p3083 ∨ (¬ p3343))
    : p3146 ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2528) := (Or.elim h111590 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112462 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116373 (p2122 p2295 p2707 p2829 : Prop)
    (h111736 : p2122 ∨ p2707 ∨ (¬ p2295) ∨ (¬ p2829))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2707 ∨ (¬ p2295) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111736 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116374 (p2122 p2553 p2707 p2829 : Prop)
    (h111737 : p2122 ∨ p2707 ∨ (¬ p2829) ∨ (¬ p2553))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2707 ∨ (¬ p2829) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111737 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116375 (p2122 p2707 p2819 p2829 : Prop)
    (h111738 : p2122 ∨ p2707 ∨ (¬ p2819) ∨ (¬ p2829))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2707 ∨ (¬ p2819) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111738 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116376 (p2122 p2707 p2829 p3483 : Prop)
    (h111739 : p2122 ∨ p2707 ∨ (¬ p3483) ∨ (¬ p2829))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2707 ∨ (¬ p3483) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116378 (p2122 p2295 p2774 p3425 : Prop)
    (h111743 : p2122 ∨ (¬ p3425) ∨ (¬ p2295) ∨ (¬ p2774))
    (h111320 : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2774))
    : (¬ p3425) ∨ (¬ p2295) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111743 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111320 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116379 (p2122 p2553 p2774 p3425 : Prop)
    (h111745 : p2122 ∨ (¬ p3425) ∨ (¬ p2774) ∨ (¬ p2553))
    (h111320 : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2774))
    : (¬ p3425) ∨ (¬ p2774) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2122 := (Or.elim h111745 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111320 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116380 (p2098 p2132 p2166 p2619 : Prop)
    (h111859 : (¬ p2619) ∨ p2166 ∨ (¬ p2098) ∨ p2132)
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : p2166 ∨ (¬ p2098) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2166) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2619) := (Or.elim h111859 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116381 (p2619 p2839 p2860 p3537 : Prop)
    (h111861 : (¬ p2619) ∨ (¬ p3537) ∨ p2860 ∨ p2839)
    (h111973 : p2619 ∨ (¬ p3537) ∨ p2839)
    : (¬ p3537) ∨ p2860 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2619) := (Or.elim h111861 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111973 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116382 (p2220 p2619 p3146 p3609 : Prop)
    (h111976 : p2619 ∨ (¬ p3146) ∨ (¬ p2220) ∨ p3609)
    (h111852 : (¬ p2619) ∨ p3609 ∨ (¬ p3146))
    : (¬ p3146) ∨ (¬ p2220) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2619 := (Or.elim h111976 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111852 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116383 (p2619 p3146 p3156 p3609 : Prop)
    (h111980 : p2619 ∨ (¬ p3156) ∨ p3609 ∨ (¬ p3146))
    (h111852 : (¬ p2619) ∨ p3609 ∨ (¬ p3146))
    : (¬ p3156) ∨ p3609 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2619 := (Or.elim h111980 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111852 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116384 (p2177 p2264 p2996 p3189 : Prop)
    (h112098 : p2264 ∨ p3189 ∨ (¬ p2177) ∨ p2996)
    (h115239 : (¬ p2264) ∨ p3189 ∨ p2996)
    : p3189 ∨ (¬ p2177) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112098 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h115239 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116385 (p2177 p2264 p2807 p3166 : Prop)
    (h112100 : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2177))
    (h115238 : (¬ p2264) ∨ (¬ p2807) ∨ p3166)
    : p3166 ∨ (¬ p2807) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112100 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115238 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116386 (p2264 p2881 p2996 p3189 : Prop)
    (h112101 : p2264 ∨ p3189 ∨ (¬ p2881) ∨ p2996)
    (h115239 : (¬ p2264) ∨ p3189 ∨ p2996)
    : p3189 ∨ (¬ p2881) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112101 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h115239 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116387 (p2264 p2449 p2807 p3166 : Prop)
    (h112104 : p2264 ∨ (¬ p2449) ∨ (¬ p2807) ∨ p3166)
    (h115238 : (¬ p2264) ∨ (¬ p2807) ∨ p3166)
    : (¬ p2449) ∨ (¬ p2807) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112104 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h115238 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116388 (p2264 p2449 p2685 p3005 : Prop)
    (h112105 : p2264 ∨ (¬ p2449) ∨ p3005 ∨ (¬ p2685))
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : (¬ p2449) ∨ p3005 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112105 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116389 (p2264 p2685 p2881 p3005 : Prop)
    (h112106 : p2264 ∨ p3005 ∨ (¬ p2881) ∨ (¬ p2685))
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : p3005 ∨ (¬ p2881) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112106 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116390 (p2264 p2807 p2911 p3166 : Prop)
    (h112109 : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2911))
    (h115238 : (¬ p2264) ∨ (¬ p2807) ∨ p3166)
    : p3166 ∨ (¬ p2807) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112109 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115238 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116391 (p2264 p2807 p2881 p3166 : Prop)
    (h112114 : p2264 ∨ p3166 ∨ (¬ p2807) ∨ (¬ p2881))
    (h115238 : (¬ p2264) ∨ (¬ p2807) ∨ p3166)
    : p3166 ∨ (¬ p2807) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h112114 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h115238 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116392 (p2156 p3125 p3323 p4032 : Prop)
    (h112416 : p3125 ∨ (¬ p4032) ∨ (¬ p3323) ∨ (¬ p2156))
    (h111429 : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156))
    : (¬ p4032) ∨ (¬ p3323) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3125 := (Or.elim h112416 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111429 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116393 (p2156 p3125 p3564 p4032 : Prop)
    (h112424 : p3125 ∨ (¬ p3564) ∨ (¬ p4032) ∨ (¬ p2156))
    (h111429 : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156))
    : (¬ p3564) ∨ (¬ p4032) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3125 := (Or.elim h112424 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111429 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116395 (p2459 p2528 p3266 p3276 : Prop)
    (h112477 : p2528 ∨ p3276 ∨ (¬ p3266) ∨ (¬ p2459))
    (h111578 : (¬ p2528) ∨ p3276 ∨ (¬ p3266))
    : p3276 ∨ (¬ p3266) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2528 := (Or.elim h112477 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111578 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116396 (p3212 p4207 p5092 p6008 : Prop)
    (h112510 : p6008 ∨ (¬ p4207) ∨ p5092 ∨ (¬ p3212))
    (h13042 : p3212 ∨ p6008)
    : p6008 ∨ (¬ p4207) ∨ p5092 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5092) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3212) := (Or.elim h112510 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h13042 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116397 (p2373 p3146 p3156 p3256 : Prop)
    (h112523 : (¬ p3156) ∨ p2373 ∨ p3146 ∨ (¬ p3256))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p2373 ∨ p3146 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3156) := (Or.elim h112523 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116398 (p2619 p3146 p3156 p3256 : Prop)
    (h112524 : (¬ p3156) ∨ p2619 ∨ p3146 ∨ (¬ p3256))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p2619 ∨ p3146 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3156) := (Or.elim h112524 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116399 (p2284 p3146 p3156 p3256 : Prop)
    (h112525 : (¬ p3156) ∨ (¬ p3256) ∨ p3146 ∨ p2284)
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : (¬ p3256) ∨ p3146 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3156) := (Or.elim h112525 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116400 (p2220 p3146 p3156 p3256 : Prop)
    (h112527 : (¬ p3156) ∨ p2220 ∨ p3146 ∨ (¬ p3256))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p2220 ∨ p3146 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3156) := (Or.elim h112527 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116401 (p2284 p2946 p3156 p3166 : Prop)
    (h112560 : p3156 ∨ p3166 ∨ (¬ p2946) ∨ (¬ p2284))
    (h112512 : (¬ p3156) ∨ p3166 ∨ (¬ p2946))
    : p3166 ∨ (¬ p2946) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3156 := (Or.elim h112560 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112512 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116402 (p2373 p3005 p3136 p3156 : Prop)
    (h112563 : p3156 ∨ p3005 ∨ (¬ p2373) ∨ (¬ p3136))
    (h112511 : (¬ p3156) ∨ p3005 ∨ (¬ p3136))
    : p3005 ∨ (¬ p2373) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3156 := (Or.elim h112563 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116403 (p2373 p2992 p3156 p3189 : Prop)
    (h112565 : p3156 ∨ p3189 ∨ (¬ p2373) ∨ (¬ p2992))
    (h112514 : (¬ p3156) ∨ p3189 ∨ (¬ p2992))
    : p3189 ∨ (¬ p2373) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3156 := (Or.elim h112565 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112514 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116404 (p2166 p2946 p3156 p3166 : Prop)
    (h112571 : p3156 ∨ p3166 ∨ (¬ p2166) ∨ (¬ p2946))
    (h112512 : (¬ p3156) ∨ p3166 ∨ (¬ p2946))
    : p3166 ∨ (¬ p2166) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3156 := (Or.elim h112571 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112512 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116405 (p2166 p3005 p3136 p3156 : Prop)
    (h112572 : p3156 ∨ p3005 ∨ (¬ p2166) ∨ (¬ p3136))
    (h112511 : (¬ p3156) ∨ p3005 ∨ (¬ p3136))
    : p3005 ∨ (¬ p2166) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3156 := (Or.elim h112572 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h112511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116406 (p2427 p2982 p3246 p3631 : Prop)
    (h112760 : (¬ p3246) ∨ p2427 ∨ p3631 ∨ (¬ p2982))
    (h107092 : p3246 ∨ p2427 ∨ (¬ p2982))
    : p2427 ∨ p3631 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112760 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h107092 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116407 (p2870 p2881 p3105 p3246 : Prop)
    (h112763 : (¬ p3246) ∨ p2881 ∨ p2870 ∨ (¬ p3105))
    (h111054 : p3246 ∨ p2870 ∨ (¬ p3105))
    : p2881 ∨ p2870 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112763 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111054 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116408 (p2881 p2891 p2972 p3246 : Prop)
    (h112764 : (¬ p3246) ∨ p2891 ∨ p2881 ∨ (¬ p2972))
    (h111056 : p3246 ∨ p2891 ∨ (¬ p2972))
    : p2891 ∨ p2881 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112764 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111056 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116409 (p2417 p2891 p2972 p3246 : Prop)
    (h112770 : (¬ p3246) ∨ p2891 ∨ p2417 ∨ (¬ p2972))
    (h111056 : p3246 ∨ p2891 ∨ (¬ p2972))
    : p2891 ∨ p2417 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112770 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111056 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116410 (p2427 p2881 p2982 p3246 : Prop)
    (h112771 : (¬ p3246) ∨ p2881 ∨ (¬ p2982) ∨ p2427)
    (h107092 : p3246 ∨ p2427 ∨ (¬ p2982))
    : p2881 ∨ (¬ p2982) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112771 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h107092 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116411 (p2417 p2901 p3115 p3246 : Prop)
    (h112774 : (¬ p3246) ∨ p2901 ∨ p2417 ∨ (¬ p3115))
    (h111053 : p3246 ∨ p2901 ∨ (¬ p3115))
    : p2901 ∨ p2417 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112774 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111053 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116412 (p2427 p2449 p2982 p3246 : Prop)
    (h112775 : (¬ p3246) ∨ p2427 ∨ p2449 ∨ (¬ p2982))
    (h107092 : p3246 ∨ p2427 ∨ (¬ p2982))
    : p2427 ∨ p2449 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112775 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h107092 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116413 (p2449 p2870 p3105 p3246 : Prop)
    (h112776 : (¬ p3246) ∨ p2870 ∨ p2449 ∨ (¬ p3105))
    (h111054 : p3246 ∨ p2870 ∨ (¬ p3105))
    : p2870 ∨ p2449 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3246) := (Or.elim h112776 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h111054 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116414 (p2156 p2829 p2839 p2860 : Prop)
    (h113142 : p2860 ∨ (¬ p2156) ∨ p2829 ∨ (¬ p2839))
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : (¬ p2156) ∨ p2829 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113142 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116415 (p2619 p2829 p2839 p2860 : Prop)
    (h113145 : p2860 ∨ (¬ p2619) ∨ (¬ p2839) ∨ p2829)
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : (¬ p2619) ∨ (¬ p2839) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113145 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116416 (p2829 p2839 p2860 p2870 : Prop)
    (h113146 : p2860 ∨ p2829 ∨ (¬ p2839) ∨ (¬ p2870))
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : p2829 ∨ (¬ p2839) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113146 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116417 (p2563 p2829 p2839 p2860 : Prop)
    (h113147 : p2860 ∨ p2829 ∨ (¬ p2563) ∨ (¬ p2839))
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : p2829 ∨ (¬ p2563) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113147 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116418 (p2284 p2829 p2839 p2860 : Prop)
    (h113148 : p2860 ∨ (¬ p2284) ∨ (¬ p2839) ∨ p2829)
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : (¬ p2284) ∨ (¬ p2839) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113148 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116419 (p2132 p2284 p2774 p2860 : Prop)
    (h113149 : p2860 ∨ (¬ p2284) ∨ (¬ p2132) ∨ p2774)
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p2284) ∨ (¬ p2132) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113149 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116420 (p2132 p2192 p2774 p2860 : Prop)
    (h113150 : p2860 ∨ (¬ p2192) ∨ p2774 ∨ (¬ p2132))
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p2192) ∨ p2774 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113150 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116421 (p2132 p2774 p2860 p3105 : Prop)
    (h113153 : p2860 ∨ (¬ p3105) ∨ (¬ p2132) ∨ p2774)
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p3105) ∨ (¬ p2132) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113153 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116422 (p2132 p2774 p2860 p2870 : Prop)
    (h113154 : p2860 ∨ (¬ p2132) ∨ p2774 ∨ (¬ p2870))
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p2132) ∨ p2774 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2860 := (Or.elim h113154 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116423 (p2192 p2563 p4210 p4338 : Prop)
    (h113261 : p2192 ∨ (¬ p4210) ∨ (¬ p2563) ∨ p4338)
    (h102260 : p4338 ∨ (¬ p2192))
    : (¬ p4210) ∨ (¬ p2563) ∨ p4338 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4338) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2192 := (Or.elim h113261 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h102260 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step116424 (p2192 p2563 p4210 p4512 : Prop)
    (h113262 : p2192 ∨ (¬ p4210) ∨ (¬ p2563) ∨ (¬ p4512))
    (h96468 : p4512 ∨ p2192)
    : p2192 ∨ (¬ p4210) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4512) := (Or.elim h113262 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96468 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116425 (p2192 p2284 p4282 p4512 : Prop)
    (h113263 : p2192 ∨ (¬ p2284) ∨ (¬ p4512) ∨ (¬ p4282))
    (h96468 : p4512 ∨ p2192)
    : p2192 ∨ (¬ p2284) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4512) := (Or.elim h113263 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96468 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116426 (p2156 p2192 p3370 p4512 : Prop)
    (h113265 : p2192 ∨ (¬ p2156) ∨ (¬ p4512) ∨ (¬ p3370))
    (h96468 : p4512 ∨ p2192)
    : p2192 ∨ (¬ p2156) ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4512) := (Or.elim h113265 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96468 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116427 (p2437 p2598 p3201 p3425 : Prop)
    (h113442 : (¬ p3201) ∨ p3425 ∨ p2437 ∨ p2598)
    (h111391 : p3201 ∨ p3425 ∨ p2598)
    : p3425 ∨ p2437 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3201) := (Or.elim h113442 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111391 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116428 (p2598 p2922 p3201 p3425 : Prop)
    (h113443 : (¬ p3201) ∨ p2922 ∨ p3425 ∨ p2598)
    (h111391 : p3201 ∨ p3425 ∨ p2598)
    : p2922 ∨ p3425 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3201) := (Or.elim h113443 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h111391 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116429 (p2122 p2156 p2274 p2860 : Prop)
    (h113504 : (¬ p2860) ∨ p2274 ∨ (¬ p2122) ∨ p2156)
    (h113138 : p2860 ∨ p2274 ∨ (¬ p2122))
    : p2274 ∨ (¬ p2122) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2860) := (Or.elim h113504 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113138 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116430 (p2187 p2819 p2860 p2870 : Prop)
    (h113507 : (¬ p2860) ∨ (¬ p2819) ∨ p2870 ∨ p2187)
    (h113139 : p2860 ∨ (¬ p2819) ∨ p2187)
    : (¬ p2819) ∨ p2870 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2860) := (Or.elim h113507 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h113139 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116432 (p2088 p2307 p2363 p2383 : Prop)
    (h114596 : (¬ p2383) ∨ (¬ p2088) ∨ p2307 ∨ p2363)
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : (¬ p2088) ∨ p2307 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2383) := (Or.elim h114596 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116433 (p2088 p2363 p2383 p2819 : Prop)
    (h114598 : (¬ p2383) ∨ p2363 ∨ p2819 ∨ (¬ p2088))
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2363 ∨ p2819 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2383) := (Or.elim h114598 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116434 (p2088 p2363 p2383 p3923 : Prop)
    (h114599 : (¬ p2383) ∨ p2363 ∨ (¬ p3923) ∨ (¬ p2088))
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2363 ∨ (¬ p3923) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2383) := (Or.elim h114599 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116435 (p2230 p2839 p2850 p3367 : Prop)
    (h115098 : p2850 ∨ p2839 ∨ (¬ p2230) ∨ (¬ p3367))
    (h106781 : p2850 ∨ p3367 ∨ (¬ p2230))
    : p2850 ∨ p2839 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3367) := (Or.elim h115098 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h106781 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116437 (p2177 p2264 p2459 p3256 : Prop)
    (h115251 : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ p2177)
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2459 ∨ (¬ p3256) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2264) := (Or.elim h115251 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116438 (p2132 p2696 p2992 p3136 : Prop)
    (h115354 : p3136 ∨ (¬ p2992) ∨ (¬ p2696) ∨ p2132)
    (h103692 : p3136 ∨ (¬ p2992) ∨ p2696)
    : p3136 ∨ (¬ p2992) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2696) := (Or.elim h115354 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h103692 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116440 (p2132 p2630 p2737 p3136 p3367 : Prop)
    (h107272 : p2630 ∨ (¬ p3136) ∨ p3367 ∨ (¬ p2737) ∨ p2132)
    (h113198 : (¬ p2630) ∨ (¬ p2737) ∨ p3367)
    : (¬ p3136) ∨ (¬ p2737) ∨ p3367 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2630 := (Or.elim h107272 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h113198 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116441 (p2122 p2608 p2829 p2839 p2860 : Prop)
    (h67515 : (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p2122))
    (h113492 : (¬ p2860) ∨ (¬ p2839) ∨ p2829)
    : (¬ p2608) ∨ (¬ p2860) ∨ (¬ p2122) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2829) := (Or.elim h67515 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h113492 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step116445 (p2156 p2284 p2901 p3246 p4032 : Prop)
    (h108332 : p3246 ∨ (¬ p4032) ∨ p2284 ∨ (¬ p2901) ∨ (¬ p2156))
    (h97948 : (¬ p2901) ∨ p2284 ∨ (¬ p2156) ∨ (¬ p3246))
    : (¬ p4032) ∨ p2284 ∨ (¬ p2901) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3246 := (Or.elim h108332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h97948 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116449 (p2363 p2761 p3266 p3516 p5580 : Prop)
    (h108986 : p3266 ∨ (¬ p3516) ∨ (¬ p5580) ∨ (¬ p2761) ∨ (¬ p2363))
    (h109249 : (¬ p3266) ∨ (¬ p5580) ∨ (¬ p2363))
    : (¬ p3516) ∨ (¬ p5580) ∨ (¬ p2761) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3266 := (Or.elim h108986 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109249 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116450 (p2088 p2098 p3537 p3599 p3609 : Prop)
    (h109015 : p3609 ∨ (¬ p2098) ∨ (¬ p2088) ∨ (¬ p3537) ∨ p3599)
    (h109456 : (¬ p3609) ∨ (¬ p3537) ∨ p3599)
    : (¬ p2098) ∨ (¬ p2088) ∨ (¬ p3537) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3609 := (Or.elim h109015 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109456 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116451 (p2717 p2753 p3425 p3434 p3599 : Prop)
    (h109282 : p3434 ∨ (¬ p2717) ∨ (¬ p2753) ∨ p3599 ∨ p3425)
    (h109671 : (¬ p3434) ∨ p3599 ∨ p3425 ∨ (¬ p2753))
    : (¬ p2717) ∨ (¬ p2753) ∨ p3599 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3434 := (Or.elim h109282 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109671 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116452 (p2630 p2737 p3599 p3755 p5177 : Prop)
    (h109290 : (¬ p3755) ∨ (¬ p5177) ∨ p2630 ∨ p2737 ∨ (¬ p3599))
    (h109469 : p3755 ∨ (¬ p3599) ∨ p2737)
    : (¬ p5177) ∨ p2630 ∨ p2737 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3755) := (Or.elim h109290 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109469 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116453 (p2230 p2406 p3193 p3276 p3707 : Prop)
    (h109385 : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p2230) ∨ p2406)
    (h110334 : (¬ p3193) ∨ p3276 ∨ (¬ p3707))
    : p3276 ∨ (¬ p3707) ∨ (¬ p2230) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3193 := (Or.elim h109385 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110334 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116454 (p2839 p2982 p3105 p3599 p4885 : Prop)
    (h109434 : (¬ p3105) ∨ (¬ p3599) ∨ p2982 ∨ (¬ p4885) ∨ p2839)
    (h108977 : p3105 ∨ (¬ p3599) ∨ p2839)
    : (¬ p3599) ∨ p2982 ∨ (¬ p4885) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3105) := (Or.elim h109434 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h108977 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116455 (p2608 p3266 p3537 p3609 p3670 : Prop)
    (h109460 : (¬ p3609) ∨ (¬ p3670) ∨ (¬ p3537) ∨ (¬ p2608) ∨ p3266)
    (h45964 : (¬ p2608) ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3670) ∨ (¬ p3537) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3266 := (Or.elim h109460 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h45964 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step116456 (p2685 p3286 p3506 p3670 p3755 : Prop)
    (h109470 : p3755 ∨ (¬ p2685) ∨ (¬ p3506) ∨ (¬ p3286) ∨ p3670)
    (h109288 : (¬ p3755) ∨ p3670 ∨ (¬ p3506))
    : (¬ p2685) ∨ (¬ p3506) ∨ (¬ p3286) ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3755 := (Or.elim h109470 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109288 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116458 (p2509 p3453 p4370 p4683 p5866 : Prop)
    (h109517 : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509))
    (h12190 : p2509 ∨ p5866)
    : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4683) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2509) := (Or.elim h109517 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h12190 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116459 (p3319 p3461 p3707 p3923 p4025 : Prop)
    (h109533 : (¬ p3319) ∨ (¬ p3707) ∨ (¬ p3923) ∨ p3461 ∨ (¬ p4025))
    (h110310 : p3319 ∨ p3461 ∨ (¬ p3707))
    : (¬ p3707) ∨ (¬ p3923) ∨ p3461 ∨ (¬ p4025) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3319) := (Or.elim h109533 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110310 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116461 (p2707 p2737 p2761 p3434 p3670 : Prop)
    (h109672 : (¬ p3434) ∨ (¬ p2707) ∨ p2737 ∨ p2761 ∨ (¬ p3670))
    (h99867 : (¬ p2707) ∨ p2737 ∨ (¬ p3434) ∨ (¬ p2761))
    : (¬ p3434) ∨ (¬ p2707) ∨ p2737 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2761 := (Or.elim h109672 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h99867 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116463 (p2707 p2737 p2761 p3434 p3670 : Prop)
    (h109827 : p3434 ∨ (¬ p2761) ∨ p3670 ∨ (¬ p2737) ∨ p2707)
    (h88409 : p2761 ∨ p3434 ∨ p2707 ∨ (¬ p2737))
    : p3434 ∨ p3670 ∨ (¬ p2737) ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2761) := (Or.elim h109827 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h88409 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116464 (p2608 p2707 p2761 p3434 p3670 : Prop)
    (h109828 : p3434 ∨ (¬ p2761) ∨ p3670 ∨ p2707 ∨ p2608)
    (h88412 : p3434 ∨ p2761 ∨ p2608 ∨ p2707)
    : p3434 ∨ p3670 ∨ p2707 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2761) := (Or.elim h109828 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h88412 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116467 (p2396 p2761 p3571 p3631 p3707 : Prop)
    (h109866 : p3631 ∨ (¬ p2396) ∨ (¬ p2761) ∨ p3707 ∨ (¬ p3571))
    (h110058 : (¬ p3631) ∨ (¬ p2761) ∨ p3707)
    : (¬ p2396) ∨ (¬ p2761) ∨ p3707 ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3631 := (Or.elim h109866 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110058 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116468 (p2341 p2707 p2717 p3537 p5261 : Prop)
    (h109919 : p2717 ∨ (¬ p5261) ∨ (¬ p2341) ∨ p3537 ∨ (¬ p2707))
    (h110684 : (¬ p2717) ∨ (¬ p2707) ∨ p3537)
    : (¬ p5261) ∨ (¬ p2341) ∨ p3537 ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5261 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2717 := (Or.elim h109919 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110684 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116469 (p2098 p2717 p2911 p3425 p5083 : Prop)
    (h109920 : p2717 ∨ p2098 ∨ (¬ p5083) ∨ (¬ p2911) ∨ p3425)
    (h110683 : (¬ p2717) ∨ p2098 ∨ p3425)
    : p2098 ∨ (¬ p5083) ∨ (¬ p2911) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2717 := (Or.elim h109920 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110683 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116471 (p3246 p3399 p3631 p3830 p4914 : Prop)
    (h110062 : (¬ p3631) ∨ (¬ p3830) ∨ p3399 ∨ (¬ p4914) ∨ p3246)
    (h109859 : p3631 ∨ (¬ p3830) ∨ p3399)
    : (¬ p3830) ∨ p3399 ∨ (¬ p4914) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3631) := (Or.elim h110062 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109859 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116472 (p2707 p3399 p3434 p3631 p3830 : Prop)
    (h110064 : (¬ p3631) ∨ (¬ p2707) ∨ (¬ p3830) ∨ p3434 ∨ p3399)
    (h109859 : p3631 ∨ (¬ p3830) ∨ p3399)
    : (¬ p2707) ∨ (¬ p3830) ∨ p3434 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3631) := (Or.elim h110064 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109859 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116473 (p2396 p3309 p3399 p3631 p3830 : Prop)
    (h110065 : (¬ p3631) ∨ (¬ p3309) ∨ (¬ p3830) ∨ p3399 ∨ p2396)
    (h109859 : p3631 ∨ (¬ p3830) ∨ p3399)
    : (¬ p3309) ∨ (¬ p3830) ∨ p3399 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3631) := (Or.elim h110065 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109859 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116474 (p2417 p2922 p3399 p3631 p3830 : Prop)
    (h110066 : (¬ p3631) ∨ (¬ p2922) ∨ p2417 ∨ p3399 ∨ (¬ p3830))
    (h109859 : p3631 ∨ (¬ p3830) ∨ p3399)
    : (¬ p2922) ∨ p2417 ∨ p3399 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3631) := (Or.elim h110066 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109859 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116475 (p2396 p3032 p3399 p3631 p3830 : Prop)
    (h110069 : (¬ p3631) ∨ (¬ p3032) ∨ (¬ p3830) ∨ p3399 ∨ p2396)
    (h109859 : p3631 ∨ (¬ p3830) ∨ p3399)
    : (¬ p3032) ∨ (¬ p3830) ∨ p3399 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3631) := (Or.elim h110069 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109859 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116477 (p2459 p3073 p3449 p3830 p4832 : Prop)
    (h110127 : p3073 ∨ p3830 ∨ (¬ p3449) ∨ (¬ p2459) ∨ (¬ p4832))
    (h110470 : (¬ p3073) ∨ (¬ p3449) ∨ p3830)
    : p3830 ∨ (¬ p3449) ∨ (¬ p2459) ∨ (¬ p4832) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3073 := (Or.elim h110127 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110470 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step116478 (p2363 p3073 p3449 p3830 p4995 : Prop)
    (h110128 : p3073 ∨ (¬ p4995) ∨ p3830 ∨ (¬ p3449) ∨ (¬ p2363))
    (h110470 : (¬ p3073) ∨ (¬ p3449) ∨ p3830)
    : (¬ p4995) ∨ p3830 ∨ (¬ p3449) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4995 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3073 := (Or.elim h110128 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110470 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116480 (p2797 p3125 p3286 p3654 p3755 : Prop)
    (h110152 : (¬ p3654) ∨ p3286 ∨ p3125 ∨ (¬ p3755) ∨ p2797)
    (h116348 : (¬ p3755) ∨ p3654 ∨ p2797)
    : p3286 ∨ p3125 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3654) := (Or.elim h110152 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h116348 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116481 (p2210 p2972 p3115 p3830 p4957 : Prop)
    (h110200 : p2972 ∨ p3830 ∨ (¬ p2210) ∨ (¬ p3115) ∨ (¬ p4957))
    (h109715 : (¬ p2972) ∨ p3830 ∨ (¬ p2210))
    : p3830 ∨ (¬ p2210) ∨ (¬ p3115) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2972 := (Or.elim h110200 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109715 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116483 (p2241 p2449 p2761 p2996 p3506 : Prop)
    (h110267 : (¬ p2449) ∨ p2761 ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2996)
    (h82037 : p2996 ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2241))
    : (¬ p2449) ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2761 := (Or.elim h110267 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82037 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116484 (p2449 p2685 p2737 p2761 p3506 : Prop)
    (h110268 : (¬ p2449) ∨ p2761 ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3506))
    (h44447 : (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p2761))
    : (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2761 := (Or.elim h110268 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h44447 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116485 (p2501 p3093 p3319 p3564 p3830 : Prop)
    (h110312 : p3319 ∨ (¬ p3564) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p2501))
    (h109714 : (¬ p3319) ∨ p3830 ∨ (¬ p3093))
    : (¬ p3564) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p2501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3319 := (Or.elim h110312 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109714 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116487 (p3093 p3309 p3319 p3323 p3830 : Prop)
    (h110314 : p3319 ∨ (¬ p3309) ∨ p3830 ∨ (¬ p3323) ∨ (¬ p3093))
    (h109714 : (¬ p3319) ∨ p3830 ∨ (¬ p3093))
    : (¬ p3309) ∨ p3830 ∨ (¬ p3323) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3319 := (Or.elim h110314 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109714 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116488 (p3093 p3319 p3323 p3830 p4024 : Prop)
    (h110318 : p3319 ∨ (¬ p3323) ∨ p3830 ∨ (¬ p4024) ∨ (¬ p3093))
    (h109714 : (¬ p3319) ∨ p3830 ∨ (¬ p3093))
    : (¬ p3323) ∨ p3830 ∨ (¬ p4024) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3319 := (Or.elim h110318 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109714 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116493 (p2187 p2819 p2829 p3537 p4342 : Prop)
    (h110453 : (¬ p2819) ∨ (¬ p4342) ∨ (¬ p3537) ∨ p2187 ∨ p2829)
    (h111541 : p2819 ∨ (¬ p3537) ∨ p2829)
    : (¬ p4342) ∨ (¬ p3537) ∨ p2187 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4342 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2819) := (Or.elim h110453 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111541 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116494 (p2528 p3073 p3266 p3707 p4690 : Prop)
    (h110474 : (¬ p3073) ∨ (¬ p4690) ∨ p2528 ∨ p3266 ∨ (¬ p3707))
    (h110124 : p3073 ∨ (¬ p3707) ∨ p3266)
    : (¬ p4690) ∨ p2528 ∨ p3266 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4690 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3073) := (Or.elim h110474 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110124 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116497 (p2717 p3399 p3576 p3631 p3830 : Prop)
    (h110534 : p3631 ∨ (¬ p3576) ∨ p3830 ∨ (¬ p3399) ∨ (¬ p2717))
    (h110600 : (¬ p3631) ∨ p3830 ∨ (¬ p3399))
    : (¬ p3576) ∨ p3830 ∨ (¬ p3399) ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3576 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3631 := (Or.elim h110534 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110600 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116498 (p2241 p2761 p3399 p3631 p3707 : Prop)
    (h110603 : (¬ p3631) ∨ p2761 ∨ (¬ p3707) ∨ p2241 ∨ (¬ p3399))
    (h97558 : (¬ p3399) ∨ p2241 ∨ (¬ p2761) ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3707) ∨ p2241 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2761 := (Or.elim h110603 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h97558 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step116499 (p2449 p2761 p2807 p2996 p3286 : Prop)
    (h110657 : (¬ p2449) ∨ (¬ p2761) ∨ p2807 ∨ (¬ p3286) ∨ p2996)
    (h110899 : p2449 ∨ (¬ p3286) ∨ p2807)
    : (¬ p2761) ∨ p2807 ∨ (¬ p3286) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2449) := (Or.elim h110657 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110899 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116504 (p2298 p2449 p2807 p3246 p3286 : Prop)
    (h110666 : (¬ p2449) ∨ p3246 ∨ (¬ p3286) ∨ (¬ p2298) ∨ p2807)
    (h110899 : p2449 ∨ (¬ p3286) ∨ p2807)
    : p3246 ∨ (¬ p3286) ∨ (¬ p2298) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2449) := (Or.elim h110666 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110899 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116505 (p2396 p2427 p2449 p2982 p4040 : Prop)
    (h110669 : (¬ p2449) ∨ (¬ p4040) ∨ (¬ p2982) ∨ p2427 ∨ p2396)
    (h116412 : p2427 ∨ p2449 ∨ (¬ p2982))
    : (¬ p4040) ∨ (¬ p2982) ∨ p2427 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2449) := (Or.elim h110669 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h116412 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116506 (p2187 p2230 p2449 p2563 p4658 : Prop)
    (h110672 : (¬ p2449) ∨ p4658 ∨ p2187 ∨ p2230 ∨ p2563)
    (h102514 : p4658 ∨ p2449)
    : p4658 ∨ p2187 ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4658) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2449) := (Or.elim h110672 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102514 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step116507 (p2459 p2608 p2707 p2717 p3609 : Prop)
    (h110686 : (¬ p2717) ∨ (¬ p3609) ∨ (¬ p2707) ∨ (¬ p2608) ∨ p2459)
    (h42667 : (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ (¬ p2707) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2459 := (Or.elim h110686 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h42667 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step116508 (p2098 p2598 p3422 p3641 p4595 : Prop)
    (h110716 : p3641 ∨ p2098 ∨ (¬ p3422) ∨ (¬ p4595) ∨ (¬ p2598))
    (h110391 : (¬ p3641) ∨ p2098 ∨ (¬ p2598))
    : p2098 ∨ (¬ p3422) ∨ (¬ p4595) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h110716 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110391 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116509 (p2098 p2528 p2598 p3367 p3641 : Prop)
    (h110718 : p3641 ∨ p2098 ∨ p2528 ∨ (¬ p2598) ∨ p3367)
    (h110391 : (¬ p3641) ∨ p2098 ∨ (¬ p2598))
    : p2098 ∨ p2528 ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h110718 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110391 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116512 (p2459 p3073 p3266 p3707 p4832 : Prop)
    (h110743 : p3073 ∨ (¬ p3266) ∨ p3707 ∨ (¬ p4832) ∨ (¬ p2459))
    (h109786 : (¬ p3073) ∨ p3707 ∨ (¬ p3266))
    : (¬ p3266) ∨ p3707 ∨ (¬ p4832) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3073 := (Or.elim h110743 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116513 (p3073 p3266 p3379 p3449 p3707 : Prop)
    (h110744 : p3073 ∨ p3707 ∨ (¬ p3379) ∨ (¬ p3266) ∨ p3449)
    (h109786 : (¬ p3073) ∨ p3707 ∨ (¬ p3266))
    : p3707 ∨ (¬ p3379) ∨ (¬ p3266) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3073 := (Or.elim h110744 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116514 (p2608 p3073 p3266 p3449 p3707 : Prop)
    (h110745 : p3073 ∨ p3707 ∨ (¬ p2608) ∨ (¬ p3266) ∨ p3449)
    (h109786 : (¬ p3073) ∨ p3707 ∨ (¬ p3266))
    : p3707 ∨ (¬ p2608) ∨ (¬ p3266) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3073 := (Or.elim h110745 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116517 (p2946 p2992 p3115 p3286 p3680 : Prop)
    (h110850 : (¬ p3115) ∨ (¬ p2992) ∨ (¬ p3680) ∨ p2946 ∨ (¬ p3286))
    (h109503 : p3115 ∨ (¬ p3286) ∨ p2946)
    : (¬ p2992) ∨ (¬ p3680) ∨ p2946 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3115) := (Or.elim h110850 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109503 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116519 (p2946 p3115 p3136 p3286 p3680 : Prop)
    (h110855 : (¬ p3115) ∨ (¬ p3286) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p3680))
    (h109503 : p3115 ∨ (¬ p3286) ∨ p2946)
    : (¬ p3286) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3115) := (Or.elim h110855 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109503 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116520 (p2156 p2957 p3115 p3136 p3755 : Prop)
    (h110859 : (¬ p3115) ∨ (¬ p3755) ∨ p2156 ∨ (¬ p2957) ∨ p3136)
    (h109505 : p3115 ∨ (¬ p3755) ∨ p3136)
    : (¬ p3755) ∨ p2156 ∨ (¬ p2957) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3115) := (Or.elim h110859 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109505 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116521 (p2331 p2797 p3286 p3323 p3461 : Prop)
    (h110876 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3286) ∨ p2331 ∨ (¬ p2797))
    (h110992 : p3323 ∨ (¬ p3286) ∨ p2331)
    : (¬ p3461) ∨ (¬ p3286) ∨ p2331 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3323) := (Or.elim h110876 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110992 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116522 (p2331 p2797 p3323 p3461 p3755 : Prop)
    (h110878 : (¬ p3323) ∨ (¬ p3755) ∨ (¬ p3461) ∨ p2797 ∨ (¬ p2331))
    (h110991 : p3323 ∨ (¬ p3755) ∨ p2797)
    : (¬ p3755) ∨ (¬ p3461) ∨ p2797 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3323) := (Or.elim h110878 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110991 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116523 (p2331 p2641 p3286 p3323 p3461 : Prop)
    (h110883 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2641) ∨ p2331 ∨ (¬ p3286))
    (h110992 : p3323 ∨ (¬ p3286) ∨ p2331)
    : (¬ p3461) ∨ (¬ p2641) ∨ p2331 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3323) := (Or.elim h110883 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110992 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116524 (p2331 p3286 p3319 p3323 p4757 : Prop)
    (h110885 : (¬ p3323) ∨ p3319 ∨ (¬ p3286) ∨ p2331 ∨ (¬ p4757))
    (h110992 : p3323 ∨ (¬ p3286) ∨ p2331)
    : p3319 ∨ (¬ p3286) ∨ p2331 ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3323) := (Or.elim h110885 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110992 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116526 (p2241 p2449 p2761 p2996 p5284 : Prop)
    (h110909 : p2449 ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p5284) ∨ p2241)
    (h99954 : p2761 ∨ p2241 ∨ p2449 ∨ (¬ p2996))
    : p2449 ∨ (¬ p2996) ∨ (¬ p5284) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2761) := (Or.elim h110909 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h99954 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116527 (p2737 p2797 p3323 p3461 p5284 : Prop)
    (h110999 : p3323 ∨ (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ p2737)
    (h110870 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3323 := (Or.elim h110999 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110870 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116528 (p2696 p2797 p3323 p3461 p5284 : Prop)
    (h111000 : p3323 ∨ p2797 ∨ p2696 ∨ (¬ p3461) ∨ (¬ p5284))
    (h82753 : p3461 ∨ p3323 ∨ p2696 ∨ p2797)
    : p3323 ∨ p2797 ∨ p2696 ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3461) := (Or.elim h111000 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h82753 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step116529 (p2881 p3399 p3449 p3527 p4914 : Prop)
    (h111026 : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p2881 ∨ (¬ p4914))
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p3449) ∨ p3399 ∨ p2881 ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h111026 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116530 (p2264 p3040 p3399 p3449 p3527 : Prop)
    (h111027 : (¬ p3527) ∨ (¬ p3449) ∨ p3399 ∨ p2264 ∨ (¬ p3040))
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p3449) ∨ p3399 ∨ p2264 ∨ (¬ p3040) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h111027 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116531 (p2707 p2717 p3399 p3449 p3527 : Prop)
    (h111032 : (¬ p3527) ∨ (¬ p2707) ∨ (¬ p3449) ∨ p3399 ∨ p2717)
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p2707) ∨ (¬ p3449) ∨ p3399 ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h111032 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116532 (p2177 p3309 p3399 p3449 p3527 : Prop)
    (h111033 : (¬ p3527) ∨ (¬ p3309) ∨ p2177 ∨ p3399 ∨ (¬ p3449))
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p3309) ∨ p2177 ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h111033 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116533 (p2911 p2922 p3399 p3449 p3527 : Prop)
    (h111034 : (¬ p3527) ∨ (¬ p2922) ∨ p3399 ∨ (¬ p3449) ∨ p2911)
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p2922) ∨ p3399 ∨ (¬ p3449) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h111034 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116534 (p2230 p2427 p2761 p3246 p4322 : Prop)
    (h111059 : p3246 ∨ (¬ p4322) ∨ p2427 ∨ p2230 ∨ (¬ p2761))
    (h81910 : p2761 ∨ p3246 ∨ p2230 ∨ p2427)
    : p3246 ∨ (¬ p4322) ∨ p2427 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2761) := (Or.elim h111059 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h81910 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116537 (p2230 p2440 p2982 p3343 p4322 : Prop)
    (h111224 : p2982 ∨ p3343 ∨ (¬ p4322) ∨ p2230 ∨ p2440)
    (h109996 : (¬ p2982) ∨ p3343 ∨ p2440)
    : p3343 ∨ (¬ p4322) ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2982 := (Or.elim h111224 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109996 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116540 (p2396 p2761 p2982 p3276 p4260 : Prop)
    (h111232 : p2982 ∨ p2761 ∨ (¬ p4260) ∨ (¬ p3276) ∨ (¬ p2396))
    (h108649 : (¬ p2761) ∨ (¬ p2396) ∨ (¬ p4260))
    : p2982 ∨ (¬ p4260) ∨ (¬ p3276) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2761 := (Or.elim h111232 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h108649 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116541 (p2440 p2727 p3343 p3842 p4953 : Prop)
    (h111257 : (¬ p3343) ∨ (¬ p3842) ∨ p2727 ∨ (¬ p4953) ∨ (¬ p2440))
    (h109936 : p3343 ∨ (¬ p3842) ∨ p2727)
    : (¬ p3842) ∨ p2727 ∨ (¬ p4953) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3842 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3343) := (Or.elim h111257 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h109936 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116544 (p2122 p2177 p2307 p2717 p2782 : Prop)
    (h111326 : (¬ p2122) ∨ (¬ p2717) ∨ p2177 ∨ p2307 ∨ (¬ p2782))
    (h106498 : p2782 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2717) ∨ p2177 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2782) := (Or.elim h111326 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h106498 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116545 (p2122 p2177 p2608 p2717 p2829 : Prop)
    (h111327 : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p2608) ∨ p2177)
    (h43080 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2608) ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2177 := (Or.elim h111327 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h43080 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116546 (p2122 p2177 p2717 p3654 p3917 : Prop)
    (h111328 : (¬ p2122) ∨ (¬ p2717) ∨ (¬ p3917) ∨ p2177 ∨ (¬ p3654))
    (h111731 : p2122 ∨ (¬ p2717) ∨ p2177)
    : (¬ p2717) ∨ (¬ p3917) ∨ p2177 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2122) := (Or.elim h111328 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111731 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116547 (p2098 p2696 p3005 p3146 p3256 : Prop)
    (h111363 : (¬ p3005) ∨ p3146 ∨ (¬ p3256) ∨ p2696 ∨ (¬ p2098))
    (h94042 : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p2696) ∨ p3146)
    : (¬ p3005) ∨ p3146 ∨ (¬ p3256) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2696 := (Or.elim h111363 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h94042 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step116549 (p2088 p2475 p3083 p3609 p3641 : Prop)
    (h111476 : p3641 ∨ p3609 ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p3083))
    (h111125 : (¬ p3641) ∨ p3609 ∨ (¬ p2475) ∨ (¬ p2088))
    : p3609 ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h111476 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111125 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116550 (p2440 p2528 p3609 p3641 p4355 : Prop)
    (h111477 : p3641 ∨ (¬ p4355) ∨ p3609 ∨ (¬ p2528) ∨ p2440)
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p4355) ∨ p3609 ∨ (¬ p2528) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h111477 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116551 (p2363 p2737 p2819 p2829 p3609 : Prop)
    (h111545 : p2819 ∨ p3609 ∨ (¬ p2363) ∨ p2829 ∨ (¬ p2737))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : p3609 ∨ (¬ p2363) ∨ p2829 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2819 := (Or.elim h111545 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116552 (p2363 p2608 p2819 p2829 p3609 : Prop)
    (h111546 : p2819 ∨ p3609 ∨ p2829 ∨ p2608 ∨ (¬ p2363))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : p3609 ∨ p2829 ∨ p2608 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2819 := (Or.elim h111546 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116553 (p2363 p2598 p2774 p2819 p3609 : Prop)
    (h111547 : p2819 ∨ p3609 ∨ (¬ p2363) ∨ p2774 ∨ (¬ p2598))
    (h86331 : p2363 ∨ p2819 ∨ (¬ p2598) ∨ p2774)
    : p2819 ∨ p3609 ∨ p2774 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2363) := (Or.elim h111547 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h86331 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116554 (p2363 p2819 p2829 p3063 p3609 : Prop)
    (h111549 : p2819 ∨ (¬ p2829) ∨ (¬ p3063) ∨ p3609 ∨ (¬ p2363))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : (¬ p2829) ∨ (¬ p3063) ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2819 := (Or.elim h111549 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116555 (p2088 p2478 p2509 p2528 p3193 : Prop)
    (h111582 : (¬ p2528) ∨ p3193 ∨ (¬ p2509) ∨ p2088 ∨ (¬ p2478))
    (h112464 : p2528 ∨ p3193 ∨ (¬ p2509))
    : p3193 ∨ (¬ p2509) ∨ p2088 ∨ (¬ p2478) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2478 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2528) := (Or.elim h111582 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112464 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116556 (p2459 p2470 p2528 p3355 p4438 : Prop)
    (h111585 : (¬ p2528) ∨ p2459 ∨ (¬ p4438) ∨ p2470 ∨ (¬ p3355))
    (h106114 : p4438 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2459 ∨ p2470 ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4438) := (Or.elim h111585 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h106114 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116557 (p2459 p2528 p3333 p3641 p4438 : Prop)
    (h111586 : (¬ p2528) ∨ p2459 ∨ p3641 ∨ (¬ p4438) ∨ (¬ p3333))
    (h106114 : p4438 ∨ (¬ p2528))
    : (¬ p2528) ∨ p2459 ∨ p3641 ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4438) := (Or.elim h111586 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h106114 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116558 (p2470 p2528 p3073 p3355 p4685 : Prop)
    (h111589 : (¬ p2528) ∨ p3073 ∨ p2470 ∨ (¬ p3355) ∨ (¬ p4685))
    (h112466 : p2528 ∨ p2470 ∨ (¬ p3355))
    : p3073 ∨ p2470 ∨ (¬ p3355) ∨ (¬ p4685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2528) := (Or.elim h111589 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112466 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116560 (p2528 p3193 p3590 p3609 p3641 : Prop)
    (h111594 : (¬ p2528) ∨ p3641 ∨ p3193 ∨ p3609 ∨ (¬ p3590))
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p2528) ∨ p3193 ∨ p3609 ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h111594 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116562 (p2363 p2528 p3083 p3343 p4383 : Prop)
    (h111602 : (¬ p2528) ∨ p2363 ∨ (¬ p4383) ∨ p3083 ∨ (¬ p3343))
    (h112462 : p2528 ∨ p3083 ∨ (¬ p3343))
    : p2363 ∨ (¬ p4383) ∨ p3083 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2528) := (Or.elim h111602 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112462 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116563 (p2122 p2274 p2774 p3425 p4889 : Prop)
    (h111740 : p2122 ∨ (¬ p2774) ∨ (¬ p2274) ∨ (¬ p3425) ∨ (¬ p4889))
    (h111320 : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2774))
    : (¬ p2774) ∨ (¬ p2274) ∨ (¬ p3425) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2122 := (Or.elim h111740 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111320 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116564 (p2122 p2396 p2774 p2829 p3425 : Prop)
    (h111744 : p2122 ∨ p2396 ∨ p2829 ∨ (¬ p2774) ∨ (¬ p3425))
    (h111320 : (¬ p2122) ∨ (¬ p3425) ∨ (¬ p2774))
    : p2396 ∨ p2829 ∨ (¬ p2774) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2122 := (Or.elim h111744 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111320 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116566 (p2122 p2274 p2707 p2829 p4390 : Prop)
    (h111754 : p2122 ∨ p2707 ∨ (¬ p4390) ∨ (¬ p2829) ∨ (¬ p2274))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2707 ∨ (¬ p4390) ∨ (¬ p2829) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2122 := (Or.elim h111754 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116567 (p2098 p2132 p2619 p2839 p3146 : Prop)
    (h111857 : (¬ p2619) ∨ (¬ p2839) ∨ (¬ p2098) ∨ (¬ p3146) ∨ p2132)
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : (¬ p2839) ∨ (¬ p2098) ∨ (¬ p3146) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h111857 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116568 (p2098 p2132 p2373 p2619 p4885 : Prop)
    (h111858 : (¬ p2619) ∨ (¬ p2098) ∨ p2373 ∨ (¬ p4885) ∨ p2132)
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : (¬ p2098) ∨ p2373 ∨ (¬ p4885) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h111858 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116569 (p2132 p2619 p2839 p3146 p3537 : Prop)
    (h111862 : (¬ p2619) ∨ (¬ p3537) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p3146))
    (h111973 : p2619 ∨ (¬ p3537) ∨ p2839)
    : (¬ p3537) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h111862 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111973 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116570 (p2373 p2619 p2839 p3537 p4885 : Prop)
    (h111863 : (¬ p2619) ∨ p2373 ∨ (¬ p3537) ∨ p2839 ∨ (¬ p4885))
    (h111973 : p2619 ∨ (¬ p3537) ∨ p2839)
    : p2373 ∨ (¬ p3537) ∨ p2839 ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h111863 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111973 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116573 (p2098 p2132 p2619 p3105 p3146 : Prop)
    (h111867 : (¬ p2619) ∨ p3146 ∨ (¬ p2098) ∨ p3105 ∨ p2132)
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : p3146 ∨ (¬ p2098) ∨ p3105 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h111867 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116575 (p2608 p2619 p2839 p3146 p3609 : Prop)
    (h111979 : p2619 ∨ p3609 ∨ (¬ p3146) ∨ p2839 ∨ p2608)
    (h84715 : p2619 ∨ p3146 ∨ p2839 ∨ p2608)
    : p2619 ∨ p3609 ∨ p2839 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3146) := (Or.elim h111979 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h84715 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116577 (p2737 p2946 p3286 p3599 p3755 : Prop)
    (h112018 : p3755 ∨ p3599 ∨ (¬ p2737) ∨ (¬ p3286) ∨ p2946)
    (h109192 : (¬ p3755) ∨ p3599 ∨ (¬ p2737))
    : p3599 ∨ (¬ p2737) ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3755 := (Or.elim h112018 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h109192 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116579 (p2264 p2685 p3005 p3040 p3527 : Prop)
    (h112107 : p2264 ∨ (¬ p3527) ∨ (¬ p2685) ∨ (¬ p3040) ∨ p3005)
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : (¬ p3527) ∨ (¬ p2685) ∨ (¬ p3040) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2264 := (Or.elim h112107 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116580 (p2264 p2685 p3005 p3931 p5564 : Prop)
    (h112108 : p2264 ∨ (¬ p3931) ∨ (¬ p5564) ∨ (¬ p2685) ∨ p3005)
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : (¬ p3931) ∨ (¬ p5564) ∨ (¬ p2685) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2264 := (Or.elim h112108 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116584 (p2241 p2459 p3073 p3399 p3527 : Prop)
    (h112234 : p3527 ∨ p3073 ∨ (¬ p2459) ∨ p3399 ∨ (¬ p2241))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : p3073 ∨ (¬ p2459) ∨ p3399 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3527 := (Or.elim h112234 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116585 (p2459 p2717 p3073 p3527 p4794 : Prop)
    (h112235 : p3527 ∨ (¬ p2717) ∨ (¬ p2459) ∨ (¬ p4794) ∨ p3073)
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : (¬ p2717) ∨ (¬ p2459) ∨ (¬ p4794) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3527 := (Or.elim h112235 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116586 (p2459 p2608 p3073 p3399 p3527 : Prop)
    (h112239 : p3527 ∨ p3073 ∨ p3399 ∨ (¬ p2459) ∨ (¬ p2608))
    (h76302 : p3527 ∨ p3399 ∨ (¬ p2608) ∨ p2459)
    : p3527 ∨ p3073 ∨ p3399 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2459) := (Or.elim h112239 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h76302 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step116587 (p2459 p2881 p3073 p3527 p4911 : Prop)
    (h112240 : p3527 ∨ (¬ p2459) ∨ p3073 ∨ (¬ p4911) ∨ (¬ p2881))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : (¬ p2459) ∨ p3073 ∨ (¬ p4911) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3527 := (Or.elim h112240 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116590 (p2192 p2563 p2972 p3125 p3461 : Prop)
    (h112423 : p3125 ∨ (¬ p2192) ∨ p2972 ∨ p2563 ∨ p3461)
    (h111428 : (¬ p3125) ∨ (¬ p2192) ∨ p2972)
    : (¬ p2192) ∨ p2972 ∨ p2563 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112423 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111428 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116591 (p2156 p2284 p3125 p3461 p4032 : Prop)
    (h112425 : p3125 ∨ p2284 ∨ (¬ p2156) ∨ p3461 ∨ (¬ p4032))
    (h111429 : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156))
    : p2284 ∨ (¬ p2156) ∨ p3461 ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112425 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111429 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116592 (p2156 p2563 p3125 p3461 p4032 : Prop)
    (h112426 : p3125 ∨ p2563 ∨ (¬ p4032) ∨ (¬ p2156) ∨ p3461)
    (h111429 : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156))
    : p2563 ∨ (¬ p4032) ∨ (¬ p2156) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112426 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111429 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116593 (p2284 p2553 p3115 p3125 p3564 : Prop)
    (h112428 : p3125 ∨ (¬ p3564) ∨ p2553 ∨ p3115 ∨ (¬ p2284))
    (h111432 : (¬ p3125) ∨ p3115 ∨ (¬ p2284))
    : (¬ p3564) ∨ p2553 ∨ p3115 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112428 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111432 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116594 (p2563 p2982 p3125 p3266 p3461 : Prop)
    (h112429 : p3125 ∨ p2982 ∨ (¬ p3266) ∨ p3461 ∨ (¬ p2563))
    (h82467 : p3461 ∨ (¬ p3266) ∨ p3125 ∨ p2563)
    : p3125 ∨ p2982 ∨ (¬ p3266) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2563) := (Or.elim h112429 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h82467 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step116595 (p2284 p2860 p3115 p3125 p3461 : Prop)
    (h112430 : p3125 ∨ p3115 ∨ (¬ p2284) ∨ p3461 ∨ p2860)
    (h111432 : (¬ p3125) ∨ p3115 ∨ (¬ p2284))
    : p3115 ∨ (¬ p2284) ∨ p3461 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112430 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111432 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116596 (p2156 p2860 p3105 p3125 p3461 : Prop)
    (h112432 : p3125 ∨ p3461 ∨ (¬ p2860) ∨ p3105 ∨ p2156)
    (h111430 : (¬ p3125) ∨ p3105 ∨ (¬ p2860))
    : p3461 ∨ (¬ p2860) ∨ p3105 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112432 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111430 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116597 (p2156 p2563 p2982 p3125 p3461 : Prop)
    (h112433 : p3125 ∨ p2982 ∨ p3461 ∨ p2156 ∨ (¬ p2563))
    (h111431 : (¬ p3125) ∨ p2982 ∨ (¬ p2563))
    : p2982 ∨ p3461 ∨ p2156 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112433 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111431 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116599 (p2274 p2284 p3115 p3125 p4620 : Prop)
    (h112437 : p3125 ∨ p3115 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4620))
    (h111432 : (¬ p3125) ∨ p3115 ∨ (¬ p2284))
    : p3115 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h112437 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111432 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116603 (p2901 p3146 p3156 p3256 p4904 : Prop)
    (h112522 : (¬ p3156) ∨ p3146 ∨ (¬ p4904) ∨ p2901 ∨ (¬ p3256))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p3146 ∨ (¬ p4904) ∨ p2901 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3156) := (Or.elim h112522 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116605 (p2901 p3146 p3156 p3256 p3988 : Prop)
    (h112536 : (¬ p3156) ∨ (¬ p3256) ∨ p3146 ∨ (¬ p3988) ∨ p2901)
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : (¬ p3256) ∨ p3146 ∨ (¬ p3988) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3156) := (Or.elim h112536 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116606 (p2427 p3146 p3156 p3256 p4119 : Prop)
    (h112539 : (¬ p3156) ∨ p3146 ∨ (¬ p4119) ∨ p2427 ∨ (¬ p3256))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p3146 ∨ (¬ p4119) ∨ p2427 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3156) := (Or.elim h112539 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116607 (p2619 p2992 p3156 p3189 p5053 : Prop)
    (h112564 : p3156 ∨ (¬ p2619) ∨ p3189 ∨ (¬ p2992) ∨ (¬ p5053))
    (h112514 : (¬ p3156) ∨ p3189 ∨ (¬ p2992))
    : (¬ p2619) ∨ p3189 ∨ (¬ p2992) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3156 := (Or.elim h112564 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112514 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116609 (p2946 p2992 p3146 p3156 p3166 : Prop)
    (h112573 : p3156 ∨ p3166 ∨ p3146 ∨ (¬ p2946) ∨ p2992)
    (h112512 : (¬ p3156) ∨ p3166 ∨ (¬ p2946))
    : p3166 ∨ p3146 ∨ (¬ p2946) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3156 := (Or.elim h112573 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112512 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116610 (p2459 p2761 p3256 p3266 p4041 : Prop)
    (h112676 : p2459 ∨ (¬ p3256) ∨ p2761 ∨ (¬ p4041) ∨ (¬ p3266))
    (h106488 : p4041 ∨ p2459)
    : p2459 ∨ (¬ p3256) ∨ p2761 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4041) := (Or.elim h112676 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h106488 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116611 (p2264 p2459 p2685 p3005 p3246 : Prop)
    (h112686 : p2459 ∨ p2264 ∨ (¬ p3246) ∨ p3005 ∨ (¬ p2685))
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : p2459 ∨ (¬ p3246) ∨ p3005 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2264 := (Or.elim h112686 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116614 (p2891 p2972 p3246 p3516 p4155 : Prop)
    (h112788 : (¬ p3246) ∨ p2891 ∨ p3516 ∨ (¬ p2972) ∨ (¬ p4155))
    (h111056 : p3246 ∨ p2891 ∨ (¬ p2972))
    : p2891 ∨ p3516 ∨ (¬ p2972) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3246) := (Or.elim h112788 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111056 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116615 (p2363 p2668 p2737 p2797 p3256 : Prop)
    (h112824 : (¬ p2668) ∨ (¬ p3256) ∨ p2363 ∨ (¬ p2797) ∨ (¬ p2737))
    (h52594 : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2797))
    : (¬ p2668) ∨ (¬ p3256) ∨ (¬ p2797) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2363 := (Or.elim h112824 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h52594 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116617 (p2132 p2274 p2774 p2839 p2860 : Prop)
    (h113158 : p2860 ∨ p2274 ∨ (¬ p2132) ∨ p2774 ∨ p2839)
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : p2274 ∨ (¬ p2132) ∨ p2774 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2860 := (Or.elim h113158 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116618 (p2132 p2187 p2774 p2839 p2860 : Prop)
    (h113159 : p2860 ∨ (¬ p2132) ∨ p2187 ∨ p2839 ∨ p2774)
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p2132) ∨ p2187 ∨ p2839 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2860 := (Or.elim h113159 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116619 (p2132 p2774 p2860 p2891 p4418 : Prop)
    (h113161 : p2860 ∨ (¬ p2891) ∨ p2774 ∨ (¬ p4418) ∨ (¬ p2132))
    (h113490 : (¬ p2860) ∨ (¬ p2132) ∨ p2774)
    : (¬ p2891) ∨ p2774 ∨ (¬ p4418) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2860 := (Or.elim h113161 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h113490 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116622 (p2630 p2797 p3333 p3343 p4972 : Prop)
    (h113212 : (¬ p2630) ∨ p3343 ∨ p2797 ∨ (¬ p3333) ∨ (¬ p4972))
    (h105837 : p4972 ∨ (¬ p2630))
    : (¬ p2630) ∨ p3343 ∨ p2797 ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4972) := (Or.elim h113212 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h105837 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116623 (p2177 p2192 p2210 p2274 p3093 : Prop)
    (h113267 : p2192 ∨ p2177 ∨ p2274 ∨ p3093 ∨ (¬ p2210))
    (h79981 : p2210 ∨ p2192 ∨ p2177 ∨ p2274)
    : p2192 ∨ p2177 ∨ p2274 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2210) := (Or.elim h113267 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h79981 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116624 (p2192 p2210 p3093 p3125 p3461 : Prop)
    (h113270 : p2192 ∨ p3461 ∨ p3125 ∨ (¬ p2210) ∨ p3093)
    (h79989 : p3461 ∨ p3125 ∨ p2210 ∨ p2192)
    : p2192 ∨ p3461 ∨ p3125 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2210) := (Or.elim h113270 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h79989 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step116625 (p2156 p2192 p2427 p2891 p4512 : Prop)
    (h113285 : p2192 ∨ (¬ p2156) ∨ (¬ p4512) ∨ p2427 ∨ (¬ p2891))
    (h96468 : p4512 ∨ p2192)
    : p2192 ∨ (¬ p2156) ∨ p2427 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4512) := (Or.elim h113285 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96468 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116626 (p2122 p2132 p2274 p2696 p2860 : Prop)
    (h113333 : p2860 ∨ (¬ p2274) ∨ (¬ p2696) ∨ p2122 ∨ p2132)
    (h99700 : p2132 ∨ p2860 ∨ p2274 ∨ (¬ p2696))
    : p2860 ∨ (¬ p2696) ∨ p2122 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2274) := (Or.elim h113333 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h99700 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116627 (p2437 p2753 p3201 p3367 p3425 : Prop)
    (h113456 : (¬ p3201) ∨ p3425 ∨ p2437 ∨ (¬ p2753) ∨ p3367)
    (h111396 : p3201 ∨ p3425 ∨ (¬ p2753) ∨ p3367)
    : p3425 ∨ p2437 ∨ (¬ p2753) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3201) := (Or.elim h113456 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111396 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116628 (p2132 p2187 p2696 p2819 p2860 : Prop)
    (h113497 : (¬ p2860) ∨ (¬ p2819) ∨ p2187 ∨ (¬ p2132) ∨ p2696)
    (h113139 : p2860 ∨ (¬ p2819) ∨ p2187)
    : (¬ p2819) ∨ p2187 ∨ (¬ p2132) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2860) := (Or.elim h113497 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h113139 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116629 (p2187 p2608 p2819 p2839 p2860 : Prop)
    (h113498 : (¬ p2860) ∨ (¬ p2819) ∨ p2187 ∨ (¬ p2608) ∨ (¬ p2839))
    (h113139 : p2860 ∨ (¬ p2819) ∨ p2187)
    : (¬ p2819) ∨ p2187 ∨ (¬ p2608) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2860) := (Or.elim h113498 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h113139 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116631 (p2839 p2860 p3125 p3367 p3483 : Prop)
    (h113500 : (¬ p2860) ∨ (¬ p3483) ∨ (¬ p2839) ∨ p3367 ∨ p3125)
    (h113140 : p2860 ∨ p3125 ∨ (¬ p3483))
    : (¬ p3483) ∨ (¬ p2839) ∨ p3367 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2860) := (Or.elim h113500 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h113140 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116633 (p2284 p2860 p3125 p3483 p5053 : Prop)
    (h113510 : (¬ p2860) ∨ p2284 ∨ p3125 ∨ (¬ p3483) ∨ (¬ p5053))
    (h105607 : p5053 ∨ (¬ p2860))
    : (¬ p2860) ∨ p2284 ∨ p3125 ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5053) := (Or.elim h113510 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h105607 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116634 (p2122 p2143 p2274 p2860 p4032 : Prop)
    (h113523 : (¬ p2860) ∨ p2274 ∨ (¬ p2122) ∨ (¬ p2143) ∨ (¬ p4032))
    (h113138 : p2860 ∨ p2274 ∨ (¬ p2122))
    : p2274 ∨ (¬ p2122) ∨ (¬ p2143) ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2860) := (Or.elim h113523 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h113138 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116635 (p2459 p2608 p2707 p2717 p3399 : Prop)
    (h113563 : p2707 ∨ p2717 ∨ p3399 ∨ p2459 ∨ (¬ p2608))
    (h88258 : p2717 ∨ p2707 ∨ p2459 ∨ p2608)
    : p2707 ∨ p2717 ∨ p3399 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2608) := (Or.elim h113563 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h88258 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step116636 (p2608 p2707 p3201 p3367 p3399 : Prop)
    (h113564 : p2707 ∨ p3201 ∨ (¬ p2608) ∨ p3399 ∨ (¬ p3367))
    (h77138 : (¬ p2608) ∨ (¬ p3367) ∨ p3399 ∨ (¬ p3201))
    : p2707 ∨ (¬ p2608) ∨ p3399 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3201 := (Or.elim h113564 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h77138 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116638 (p2122 p2396 p2608 p2829 p3093 : Prop)
    (h113615 : p2829 ∨ p2122 ∨ p2396 ∨ p3093 ∨ (¬ p2608))
    (h97874 : p2829 ∨ p2608 ∨ p2122 ∨ p2396)
    : p2829 ∨ p2122 ∨ p2396 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2608) := (Or.elim h113615 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h97874 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116639 (p2177 p2241 p2264 p2295 p2641 : Prop)
    (h113680 : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2241) ∨ p2177 ∨ (¬ p2264))
    (h43081 : (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641))
    : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2177 := (Or.elim h113680 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h43081 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116643 (p2696 p2774 p2797 p3323 p3461 : Prop)
    (h113917 : p2797 ∨ p3461 ∨ p2774 ∨ (¬ p2696) ∨ p3323)
    (h82753 : p3461 ∨ p3323 ∨ p2696 ∨ p2797)
    : p2797 ∨ p3461 ∨ p2774 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2696) := (Or.elim h113917 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82753 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step116644 (p2274 p2295 p2737 p2797 p2829 : Prop)
    (h113926 : p2797 ∨ p2295 ∨ (¬ p2737) ∨ (¬ p2274) ∨ p2829)
    (h98627 : p2797 ∨ p2295 ∨ p2737 ∨ (¬ p2274))
    : p2797 ∨ p2295 ∨ (¬ p2274) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2737) := (Or.elim h113926 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h98627 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116646 (p2630 p2946 p3016 p3136 p3422 : Prop)
    (h114047 : p2630 ∨ (¬ p3016) ∨ (¬ p3136) ∨ p2946 ∨ p3422)
    (h84278 : (¬ p3136) ∨ p3016 ∨ p2946 ∨ p2630)
    : p2630 ∨ (¬ p3136) ∨ p2946 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3016) := (Or.elim h114047 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h84278 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step116647 (p2187 p2284 p2668 p2727 p2992 : Prop)
    (h114116 : (¬ p2284) ∨ (¬ p2992) ∨ p2727 ∨ (¬ p2668) ∨ p2187)
    (h85919 : (¬ p2284) ∨ (¬ p2187) ∨ p2727 ∨ (¬ p2992))
    : (¬ p2284) ∨ (¬ p2992) ∨ p2727 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2187 := (Or.elim h114116 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h85919 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116648 (p2417 p2761 p2922 p3379 p3399 : Prop)
    (h114252 : (¬ p2922) ∨ (¬ p2761) ∨ (¬ p2417) ∨ p3379 ∨ (¬ p3399))
    (h45257 : (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3379))
    : (¬ p2922) ∨ (¬ p2761) ∨ (¬ p2417) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3379 := (Or.elim h114252 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h45257 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116649 (p2459 p2911 p2922 p3379 p3399 : Prop)
    (h114254 : (¬ p2922) ∨ (¬ p3399) ∨ p3379 ∨ (¬ p2911) ∨ (¬ p2459))
    (h42850 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379))
    : (¬ p2922) ∨ (¬ p3399) ∨ (¬ p2911) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3379 := (Or.elim h114254 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h42850 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step116652 (p2396 p2437 p2449 p2807 p3286 : Prop)
    (h114327 : p2437 ∨ (¬ p2449) ∨ p2396 ∨ p2807 ∨ (¬ p3286))
    (h110899 : p2449 ∨ (¬ p3286) ∨ p2807)
    : p2437 ∨ p2396 ∨ p2807 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2449) := (Or.elim h114327 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h110899 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116653 (p2459 p2528 p2598 p2911 p3201 : Prop)
    (h114529 : p2911 ∨ p2528 ∨ p3201 ∨ p2598 ∨ (¬ p2459))
    (h97512 : p2911 ∨ p2459 ∨ p2598 ∨ p3201)
    : p2911 ∨ p2528 ∨ p3201 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2459) := (Or.elim h114529 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h97512 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116654 (p2437 p2459 p2528 p2651 p2911 : Prop)
    (h114530 : p2911 ∨ p2528 ∨ (¬ p2459) ∨ p2437 ∨ p2651)
    (h75139 : p2911 ∨ p2459 ∨ p2437 ∨ p2651)
    : p2911 ∨ p2528 ∨ p2437 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2459) := (Or.elim h114530 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h75139 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116656 (p2088 p2295 p2363 p2383 p3955 : Prop)
    (h114604 : (¬ p2383) ∨ p2363 ∨ (¬ p2088) ∨ (¬ p3955) ∨ p2295)
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2363 ∨ (¬ p2088) ∨ (¬ p3955) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2383) := (Or.elim h114604 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116657 (p2088 p2274 p2363 p2383 p3743 : Prop)
    (h114605 : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2088) ∨ p2363 ∨ p2274)
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : (¬ p3743) ∨ (¬ p2088) ∨ p2363 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2383) := (Or.elim h114605 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116658 (p2088 p2274 p2363 p2383 p3955 : Prop)
    (h114606 : (¬ p2383) ∨ p2363 ∨ (¬ p2088) ∨ p2274 ∨ (¬ p3955))
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2363 ∨ (¬ p2088) ∨ p2274 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2383) := (Or.elim h114606 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116661 (p2241 p2284 p2440 p2563 p2727 : Prop)
    (h114843 : (¬ p2440) ∨ p2284 ∨ p2241 ∨ (¬ p2563) ∨ p2727)
    (h80865 : p2727 ∨ p2241 ∨ (¬ p2440) ∨ p2563)
    : (¬ p2440) ∨ p2284 ∨ p2241 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2563) := (Or.elim h114843 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h80865 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step116663 (p2427 p2437 p2440 p2891 p4629 : Prop)
    (h115021 : (¬ p2427) ∨ p2891 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4629))
    (h106081 : p4629 ∨ (¬ p2427))
    : (¬ p2427) ∨ p2891 ∨ (¬ p2437) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4629) := (Or.elim h115021 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h106081 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116665 (p2274 p2563 p2839 p2850 p3367 : Prop)
    (h115100 : p2850 ∨ p2274 ∨ p2563 ∨ (¬ p3367) ∨ p2839)
    (h75544 : p2274 ∨ p2850 ∨ p3367 ∨ p2563)
    : p2850 ∨ p2274 ∨ p2563 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3367) := (Or.elim h115100 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h75544 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step116667 (p2177 p2459 p2553 p2573 p3389 : Prop)
    (h115162 : p2553 ∨ p2459 ∨ p3389 ∨ (¬ p2573) ∨ p2177)
    (h101073 : p2177 ∨ p2553 ∨ p2459 ∨ p2573)
    : p2553 ∨ p2459 ∨ p3389 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2573) := (Or.elim h115162 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h101073 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step116668 (p2264 p2459 p2911 p3256 p4653 : Prop)
    (h115250 : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ (¬ p4653) ∨ p2911)
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2459 ∨ (¬ p3256) ∨ (¬ p4653) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2264) := (Or.elim h115250 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116669 (p2241 p2264 p2459 p2996 p3256 : Prop)
    (h115253 : (¬ p2264) ∨ (¬ p3256) ∨ p2459 ∨ (¬ p2241) ∨ p2996)
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : (¬ p3256) ∨ p2459 ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2264) := (Or.elim h115253 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116670 (p2264 p2459 p2685 p2696 p3256 : Prop)
    (h115254 : (¬ p2264) ∨ p2459 ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p2685))
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2459 ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2264) := (Or.elim h115254 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116673 (p2132 p2274 p2284 p2696 p3136 : Prop)
    (h115352 : p3136 ∨ p2274 ∨ p2284 ∨ (¬ p2696) ∨ p2132)
    (h82647 : p3136 ∨ p2696 ∨ p2284 ∨ p2274)
    : p3136 ∨ p2274 ∨ p2284 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2696) := (Or.elim h115352 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h82647 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step116674 (p2098 p2132 p2284 p2619 p3136 : Prop)
    (h115361 : p3136 ∨ (¬ p2619) ∨ (¬ p2098) ∨ p2284 ∨ p2132)
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : p3136 ∨ (¬ p2098) ∨ p2284 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2619) := (Or.elim h115361 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116678 (p2177 p2264 p2341 p4009 p5590 : Prop)
    (h115608 : p2341 ∨ p2264 ∨ (¬ p4009) ∨ (¬ p2177) ∨ (¬ p5590))
    (h104070 : (¬ p2264) ∨ p2341)
    : p2341 ∨ (¬ p4009) ∨ (¬ p2177) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2264 := (Or.elim h115608 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h104070 (fun q0 => (False.elim (q0 u4))) (fun r0 => (False.elim (u0 r0)))))

theorem step116679 (p2177 p2341 p2881 p3051 p4238 : Prop)
    (h115614 : p2341 ∨ (¬ p2177) ∨ p2881 ∨ p3051 ∨ (¬ p4238))
    (h107085 : p2881 ∨ (¬ p2341) ∨ p3051)
    : (¬ p2177) ∨ p2881 ∨ p3051 ∨ (¬ p4238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2341 := (Or.elim h115614 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h107085 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116680 (p2156 p3125 p3461 p4032 p5442 : Prop)
    (h115715 : p5442 ∨ p3125 ∨ (¬ p3461) ∨ (¬ p4032) ∨ (¬ p2156))
    (h111429 : (¬ p3125) ∨ (¬ p4032) ∨ (¬ p2156))
    : p5442 ∨ (¬ p3461) ∨ (¬ p4032) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3125 := (Or.elim h115715 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h111429 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116681 (p3032 p3399 p3449 p3527 p6143 : Prop)
    (h116171 : (¬ p6143) ∨ (¬ p3527) ∨ (¬ p3032) ∨ p3399 ∨ (¬ p3449))
    (h112231 : p3527 ∨ (¬ p3449) ∨ p3399)
    : (¬ p6143) ∨ (¬ p3032) ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3527) := (Or.elim h116171 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h112231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116683 (p2098 p2598 p3641 p4149 p5612 : Prop)
    (h116242 : p5612 ∨ p3641 ∨ p4149 ∨ (¬ p2598) ∨ p2098)
    (h110391 : (¬ p3641) ∨ p2098 ∨ (¬ p2598))
    : p5612 ∨ p4149 ∨ (¬ p2598) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5612) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3641 := (Or.elim h116242 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h110391 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116684 (p2373 p2440 p2510 p3016 p3156 p3422 : Prop)
    (h107378 : (¬ p3422) ∨ p3156 ∨ (¬ p2440) ∨ p3016 ∨ (¬ p2373) ∨ (¬ p2510))
    (h114847 : (¬ p2440) ∨ p3156 ∨ (¬ p2373) ∨ (¬ p3016))
    : (¬ p2373) ∨ (¬ p2440) ∨ (¬ p3422) ∨ p3156 ∨ (¬ p2510) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3016 := (Or.elim h107378 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h114847 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step116688 (p2177 p2192 p2210 p2274 p2608 p3073 : Prop)
    (h107438 : (¬ p3073) ∨ (¬ p2210) ∨ p2608 ∨ (¬ p2192) ∨ p2274 ∨ (¬ p2177))
    (h97472 : p2608 ∨ (¬ p2274) ∨ (¬ p2192) ∨ (¬ p2210))
    : (¬ p2192) ∨ (¬ p2177) ∨ (¬ p2210) ∨ p2608 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2274 := (Or.elim h107438 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h97472 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step116690 (p2264 p2437 p2630 p2685 p2737 p3425 : Prop)
    (h107446 : p2737 ∨ p2630 ∨ p2264 ∨ p2685 ∨ (¬ p3425) ∨ p2437)
    (h113973 : p2437 ∨ (¬ p2685) ∨ p2630)
    : p2264 ∨ p2437 ∨ (¬ p3425) ∨ p2630 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2685 := (Or.elim h107446 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h113973 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116691 (p2264 p2685 p2911 p3005 p3166 p4236 : Prop)
    (h103744 : (¬ p4236) ∨ p3166 ∨ (¬ p2911) ∨ p3005 ∨ (¬ p2685) ∨ p2264)
    (h115240 : (¬ p2264) ∨ (¬ p2685) ∨ p3005)
    : (¬ p2911) ∨ (¬ p2685) ∨ (¬ p4236) ∨ p3166 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2264 := (Or.elim h103744 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h115240 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step116693 (p2156 p2284 p2901 p2972 p3246 p3370 : Prop)
    (h108333 : p3246 ∨ p2284 ∨ (¬ p2156) ∨ (¬ p2901) ∨ p2972 ∨ (¬ p3370))
    (h97948 : (¬ p2901) ∨ p2284 ∨ (¬ p2156) ∨ (¬ p3246))
    : p2284 ∨ (¬ p2156) ∨ (¬ p2901) ∨ p2972 ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3246 := (Or.elim h108333 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h97948 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step116697 (p2230 p3193 p3276 p3347 p3707 p4953 : Prop)
    (h109387 : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p3347) ∨ p2230 ∨ (¬ p4953))
    (h110334 : (¬ p3193) ∨ p3276 ∨ (¬ p3707))
    : p3276 ∨ (¬ p3707) ∨ (¬ p3347) ∨ p2230 ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3193 := (Or.elim h109387 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h110334 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116699 (p2707 p2761 p3367 p3516 p3773 p3959 : Prop)
    (h109447 : p3516 ∨ (¬ p2761) ∨ (¬ p3959) ∨ (¬ p3367) ∨ p2707 ∨ (¬ p3773))
    (h88408 : p2761 ∨ p3516 ∨ (¬ p3367) ∨ p2707 ∨ (¬ p3959))
    : p3516 ∨ (¬ p3959) ∨ (¬ p3367) ∨ p2707 ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2761) := (Or.elim h109447 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h88408 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step116707 (p2295 p3093 p3319 p3830 p3922 p4620 : Prop)
    (h110320 : p3319 ∨ (¬ p2295) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4620))
    (h109714 : (¬ p3319) ∨ p3830 ∨ (¬ p3093))
    : (¬ p2295) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3319 := (Or.elim h110320 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h109714 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116720 (p2563 p2630 p2651 p2982 p3286 p3343 : Prop)
    (h111273 : (¬ p3343) ∨ p2982 ∨ (¬ p3286) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2563))
    (h109938 : p3343 ∨ (¬ p3286) ∨ p2651)
    : p2982 ∨ (¬ p3286) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3343) := (Or.elim h111273 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h109938 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116723 (p2284 p2946 p3125 p3322 p3461 p3680 : Prop)
    (h111447 : (¬ p3125) ∨ (¬ p3322) ∨ p3461 ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p2284))
    (h43226 : (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p3125) ∨ (¬ p3322) ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3461 := (Or.elim h111447 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h43226 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step116726 (p2510 p2528 p2553 p3367 p3609 p3641 : Prop)
    (h111472 : p3641 ∨ (¬ p2510) ∨ p2553 ∨ (¬ p2528) ∨ p3609 ∨ p3367)
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p2510) ∨ p2553 ∨ (¬ p2528) ∨ p3609 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3641 := (Or.elim h111472 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116727 (p2528 p2573 p3422 p3609 p3641 p3905 : Prop)
    (h111473 : p3641 ∨ p2573 ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p2528) ∨ p3609)
    (h77610 : p3641 ∨ p2528 ∨ (¬ p3422) ∨ p2573)
    : p3641 ∨ p2573 ∨ (¬ p3422) ∨ (¬ p3905) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2528) := (Or.elim h111473 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h77610 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step116729 (p2088 p2528 p3083 p3343 p3858 p4685 : Prop)
    (h111600 : (¬ p2528) ∨ (¬ p4685) ∨ p3083 ∨ (¬ p3343) ∨ (¬ p3858) ∨ p2088)
    (h112462 : p2528 ∨ p3083 ∨ (¬ p3343))
    : (¬ p4685) ∨ p3083 ∨ (¬ p3343) ∨ (¬ p3858) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2528) := (Or.elim h111600 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h112462 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116731 (p2122 p2177 p2707 p2774 p2829 p3873 : Prop)
    (h111759 : p2122 ∨ p2177 ∨ p2774 ∨ (¬ p2829) ∨ p2707 ∨ (¬ p3873))
    (h111319 : (¬ p2122) ∨ p2707 ∨ (¬ p2829))
    : p2177 ∨ p2774 ∨ (¬ p2829) ∨ p2707 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2122 := (Or.elim h111759 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111319 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116733 (p2459 p2696 p2717 p3005 p3256 p3425 : Prop)
    (h111792 : p2717 ∨ p3005 ∨ p3256 ∨ (¬ p2696) ∨ (¬ p3425) ∨ (¬ p2459))
    (h82627 : p3005 ∨ p3256 ∨ (¬ p2459) ∨ p2696)
    : p2717 ∨ p3005 ∨ p3256 ∨ (¬ p3425) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2696) := (Or.elim h111792 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h82627 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u5 r2)))))))))

theorem step116734 (p2122 p2396 p2417 p2598 p2774 p4106 : Prop)
    (h111825 : p2122 ∨ (¬ p2598) ∨ p2417 ∨ (¬ p2396) ∨ (¬ p4106) ∨ p2774)
    (h97876 : p2774 ∨ p2122 ∨ p2396 ∨ (¬ p2598))
    : p2122 ∨ (¬ p2598) ∨ p2417 ∨ (¬ p4106) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2396) := (Or.elim h111825 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h97876 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step116737 (p2331 p2651 p3276 p3323 p3343 p3461 : Prop)
    (h111947 : (¬ p3323) ∨ (¬ p3343) ∨ (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p2331))
    (h111936 : (¬ p3323) ∨ p3343 ∨ (¬ p2331) ∨ p2651)
    : (¬ p3323) ∨ (¬ p3276) ∨ p3461 ∨ p2651 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3343) := (Or.elim h111947 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111936 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116739 (p2459 p2598 p3073 p3425 p3527 p3576 : Prop)
    (h112242 : p3527 ∨ p3073 ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p2459) ∨ (¬ p3576))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : p3073 ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p2459) ∨ (¬ p3576) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3527 := (Or.elim h112242 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116744 (p2192 p2553 p2972 p3096 p3125 p4620 : Prop)
    (h112440 : p3125 ∨ (¬ p2192) ∨ (¬ p3096) ∨ (¬ p2553) ∨ p2972 ∨ (¬ p4620))
    (h111428 : (¬ p3125) ∨ (¬ p2192) ∨ p2972)
    : (¬ p2192) ∨ (¬ p3096) ∨ (¬ p2553) ∨ p2972 ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3125 := (Or.elim h112440 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111428 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116752 (p2946 p3005 p3136 p3156 p4236 p5568 : Prop)
    (h112584 : p3156 ∨ p3005 ∨ (¬ p5568) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p4236))
    (h112511 : (¬ p3156) ∨ p3005 ∨ (¬ p3136))
    : p3005 ∨ (¬ p5568) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3156 := (Or.elim h112584 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h112511 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step116753 (p2946 p3005 p3136 p3146 p3156 p4236 : Prop)
    (h112585 : p3156 ∨ p3146 ∨ p3005 ∨ (¬ p3136) ∨ (¬ p4236) ∨ p2946)
    (h112511 : (¬ p3156) ∨ p3005 ∨ (¬ p3136))
    : p3146 ∨ p3005 ∨ (¬ p3136) ∨ (¬ p4236) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3156 := (Or.elim h112585 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h112511 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116757 (p2427 p2761 p2982 p3051 p3246 p4399 : Prop)
    (h112791 : (¬ p3246) ∨ (¬ p2761) ∨ p2427 ∨ (¬ p3051) ∨ (¬ p4399) ∨ (¬ p2982))
    (h107092 : p3246 ∨ p2427 ∨ (¬ p2982))
    : (¬ p2761) ∨ p2427 ∨ (¬ p3051) ∨ (¬ p4399) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3246) := (Or.elim h112791 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h107092 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116758 (p2901 p3115 p3246 p3576 p3631 p4895 : Prop)
    (h112792 : (¬ p3246) ∨ (¬ p3576) ∨ p2901 ∨ (¬ p4895) ∨ p3631 ∨ (¬ p3115))
    (h111053 : p3246 ∨ p2901 ∨ (¬ p3115))
    : (¬ p3576) ∨ p2901 ∨ (¬ p4895) ∨ p3631 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3576 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3246) := (Or.elim h112792 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111053 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116761 (p2417 p2753 p2761 p3201 p3367 p3425 : Prop)
    (h113452 : (¬ p3201) ∨ (¬ p2761) ∨ p3425 ∨ (¬ p2417) ∨ p3367 ∨ (¬ p2753))
    (h111396 : p3201 ∨ p3425 ∨ (¬ p2753) ∨ p3367)
    : (¬ p2761) ∨ p3425 ∨ (¬ p2417) ∨ p3367 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3201) := (Or.elim h113452 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111396 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116764 (p2440 p2598 p3201 p3425 p4030 p4116 : Prop)
    (h113469 : (¬ p3201) ∨ p3425 ∨ (¬ p2440) ∨ (¬ p4030) ∨ (¬ p4116) ∨ p2598)
    (h111391 : p3201 ∨ p3425 ∨ p2598)
    : p3425 ∨ (¬ p2440) ∨ (¬ p4030) ∨ (¬ p4116) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3201) := (Or.elim h113469 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h111391 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step116765 (p2122 p2284 p2307 p2860 p4356 p5053 : Prop)
    (h113522 : (¬ p2860) ∨ p2284 ∨ (¬ p4356) ∨ (¬ p5053) ∨ (¬ p2122) ∨ p2307)
    (h105607 : p5053 ∨ (¬ p2860))
    : (¬ p2860) ∨ p2284 ∨ (¬ p4356) ∨ (¬ p2122) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5053) := (Or.elim h113522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h105607 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step116767 (p2122 p2563 p2829 p2982 p3125 p3319 : Prop)
    (h113633 : p2829 ∨ p3125 ∨ p2982 ∨ p2122 ∨ (¬ p3319) ∨ (¬ p2563))
    (h111431 : (¬ p3125) ∨ p2982 ∨ (¬ p2563))
    : p2829 ∨ p2982 ∨ p2122 ∨ (¬ p3319) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3125 := (Or.elim h113633 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h111431 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116768 (p2396 p2459 p3256 p3266 p3461 p4041 : Prop)
    (h113825 : (¬ p2396) ∨ p2459 ∨ (¬ p3256) ∨ p3461 ∨ (¬ p4041) ∨ (¬ p3266))
    (h106488 : p4041 ∨ p2459)
    : (¬ p2396) ∨ p2459 ∨ (¬ p3256) ∨ p3461 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4041) := (Or.elim h113825 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h106488 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step116769 (p2274 p2284 p2307 p2630 p3136 p3567 : Prop)
    (h114137 : (¬ p2284) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p3136) ∨ p2630 ∨ (¬ p3567))
    (h84272 : (¬ p3136) ∨ (¬ p2274) ∨ p2630 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3136) ∨ p2630 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2274 := (Or.elim h114137 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h84272 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step116774 (p2459 p2528 p2911 p3363 p3367 p3389 : Prop)
    (h114534 : p2911 ∨ (¬ p3363) ∨ p2528 ∨ p3389 ∨ p3367 ∨ (¬ p2459))
    (h75586 : p2911 ∨ p2459 ∨ p3389 ∨ (¬ p3363) ∨ p3367)
    : p2911 ∨ (¬ p3363) ∨ p2528 ∨ p3389 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h114534 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h75586 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3)))))))))))

theorem step116775 (p2437 p2440 p2459 p2911 p3146 p3693 : Prop)
    (h114540 : p2911 ∨ p3146 ∨ (¬ p2459) ∨ p2440 ∨ p2437 ∨ (¬ p3693))
    (h74558 : p2911 ∨ p2459 ∨ p2440 ∨ p2437)
    : p2911 ∨ p3146 ∨ p2440 ∨ p2437 ∨ (¬ p3693) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h114540 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h74558 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step116776 (p2459 p2528 p2662 p2727 p2911 p3389 : Prop)
    (h114545 : p2911 ∨ p3389 ∨ p2528 ∨ (¬ p2662) ∨ p2727 ∨ (¬ p2459))
    (h99994 : p2911 ∨ p2459 ∨ p3389 ∨ p2727 ∨ (¬ p2662))
    : p2911 ∨ p3389 ∨ p2528 ∨ (¬ p2662) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h114545 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h99994 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step116777 (p2098 p2437 p2440 p2598 p2911 p3641 : Prop)
    (h114547 : p2911 ∨ (¬ p3641) ∨ (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598)
    (h111465 : p3641 ∨ (¬ p2098) ∨ p2598)
    : p2911 ∨ (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3641) := (Or.elim h114547 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h111465 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step116778 (p2088 p2352 p2363 p2383 p2507 p5016 : Prop)
    (h114602 : (¬ p2383) ∨ p2352 ∨ p2363 ∨ (¬ p5016) ∨ (¬ p2507) ∨ (¬ p2088))
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2352 ∨ p2363 ∨ (¬ p5016) ∨ (¬ p2507) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2383) := (Or.elim h114602 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116780 (p2088 p2363 p2383 p2630 p2797 p3567 : Prop)
    (h114614 : (¬ p2383) ∨ (¬ p2797) ∨ (¬ p2088) ∨ p2363 ∨ p2630 ∨ (¬ p3567))
    (h92217 : (¬ p2383) ∨ (¬ p2363) ∨ (¬ p2797) ∨ (¬ p3567) ∨ p2630)
    : (¬ p2383) ∨ (¬ p2797) ∨ (¬ p2088) ∨ p2630 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2363 := (Or.elim h114614 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h92217 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step116782 (p2088 p2341 p2459 p2707 p2737 p3577 : Prop)
    (h114684 : (¬ p2341) ∨ (¬ p2088) ∨ (¬ p3577) ∨ (¬ p2707) ∨ p2459 ∨ p2737)
    (h101682 : (¬ p2707) ∨ (¬ p3577) ∨ p2737 ∨ (¬ p2341) ∨ (¬ p2459))
    : (¬ p2341) ∨ (¬ p2088) ∨ (¬ p3577) ∨ (¬ p2707) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2459 := (Or.elim h114684 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h101682 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step116784 (p2132 p2440 p2696 p2797 p3136 p4972 : Prop)
    (h114888 : (¬ p2440) ∨ (¬ p3136) ∨ (¬ p2132) ∨ p2797 ∨ p2696 ∨ (¬ p4972))
    (h105889 : p4972 ∨ (¬ p3136))
    : (¬ p2440) ∨ (¬ p3136) ∨ (¬ p2132) ∨ p2797 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4972) := (Or.elim h114888 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h105889 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step116788 (p2088 p2341 p2459 p2707 p3367 p3959 : Prop)
    (h115611 : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p3367) ∨ (¬ p2459))
    (h88396 : p2341 ∨ p2707 ∨ p2459 ∨ (¬ p3959) ∨ (¬ p3367))
    : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h115611 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h88396 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step116789 (p2088 p2341 p2459 p2630 p2685 p4155 : Prop)
    (h115621 : p2341 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p2459) ∨ p2088 ∨ (¬ p4155))
    (h101778 : p2341 ∨ p2459 ∨ (¬ p4155) ∨ (¬ p2630) ∨ p2685)
    : p2341 ∨ p2685 ∨ (¬ p2630) ∨ p2088 ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h115621 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h101778 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step116790 (p2088 p2341 p2459 p2707 p2737 p3959 : Prop)
    (h115622 : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p2737) ∨ (¬ p2459))
    (h88399 : p2341 ∨ (¬ p2737) ∨ (¬ p3959) ∨ p2459 ∨ p2707)
    : p2341 ∨ (¬ p3959) ∨ p2707 ∨ p2088 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2459) := (Or.elim h115622 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h88399 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step116792 (p2187 p2241 p2352 p2383 p3379 p3449 p4756 : Prop)
    (h107473 : p3449 ∨ (¬ p2187) ∨ (¬ p3379) ∨ (¬ p2352) ∨ p2383 ∨ (¬ p4756) ∨ (¬ p2241))
    (h106434 : p4756 ∨ (¬ p2241))
    : (¬ p2352) ∨ p3449 ∨ (¬ p2187) ∨ (¬ p3379) ∨ p2383 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4756) := (Or.elim h107473 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h106434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step116794 (p2241 p2992 p3115 p3266 p3461 p3654 p4450 : Prop)
    (h107516 : p3461 ∨ (¬ p3266) ∨ (¬ p4450) ∨ (¬ p2992) ∨ p3654 ∨ (¬ p2241) ∨ (¬ p3115))
    (h106564 : p4450 ∨ (¬ p3115))
    : p3461 ∨ (¬ p2992) ∨ p3654 ∨ (¬ p3266) ∨ (¬ p2241) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4450) := (Or.elim h107516 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h106564 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step116797 (p2264 p2437 p2440 p2459 p2659 p3389 p3575 : Prop)
    (h107523 : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3575) ∨ p3389 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2659))
    (h91423 : p3575 ∨ p3389)
    : (¬ p2459) ∨ (¬ p2437) ∨ (¬ p2264) ∨ p3389 ∨ (¬ p2659) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3575) := (Or.elim h107523 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h91423 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step116798 (p2132 p2352 p2528 p2598 p2630 p2727 p3573 : Prop)
    (h107533 : p2132 ∨ (¬ p2598) ∨ p2630 ∨ p2352 ∨ (¬ p3573) ∨ (¬ p2727) ∨ p2528)
    (h102496 : p3573 ∨ p2352)
    : (¬ p2727) ∨ p2630 ∨ (¬ p2598) ∨ p2352 ∨ p2528 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3573) := (Or.elim h107533 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (u4 r5))))))))))))));
    (Or.elim h102496 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step116808 (p2651 p3016 p3073 p3266 p3449 p3564 p3707 : Prop)
    (h110761 : p3073 ∨ (¬ p3564) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p3449 ∨ (¬ p3266) ∨ p3707)
    (h109786 : (¬ p3073) ∨ p3707 ∨ (¬ p3266))
    : (¬ p3564) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p3449 ∨ (¬ p3266) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3073 := (Or.elim h110761 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h109786 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116809 (p2331 p2518 p2528 p3323 p3379 p3461 p5284 : Prop)
    (h111017 : p3323 ∨ (¬ p3461) ∨ (¬ p2518) ∨ p2331 ∨ (¬ p2528) ∨ (¬ p5284) ∨ (¬ p3379))
    (h110870 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p5284))
    : (¬ p3461) ∨ (¬ p2518) ∨ p2331 ∨ (¬ p2528) ∨ (¬ p5284) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3323 := (Or.elim h111017 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h110870 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116811 (p2192 p2210 p2274 p2598 p2717 p2911 p3201 : Prop)
    (h111421 : p3201 ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2911) ∨ p2598 ∨ p2717 ∨ (¬ p2274))
    (h113432 : (¬ p3201) ∨ p2717 ∨ (¬ p2911))
    : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2911) ∨ p2598 ∨ p2717 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3201 := (Or.elim h111421 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h113432 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116814 (p2363 p2373 p2406 p2774 p2819 p3379 p3609 : Prop)
    (h111565 : p2819 ∨ (¬ p2373) ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2774 ∨ p3609 ∨ (¬ p2363))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : (¬ p2373) ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2774 ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2819 := (Or.elim h111565 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step116815 (p2241 p2363 p2774 p2819 p2992 p3156 p3609 : Prop)
    (h111571 : p2819 ∨ p3609 ∨ (¬ p2992) ∨ (¬ p2363) ∨ p2774 ∨ (¬ p2241) ∨ (¬ p3156))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : p3609 ∨ (¬ p2992) ∨ (¬ p2363) ∨ p2774 ∨ (¬ p2241) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2819 := (Or.elim h111571 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116819 (p2132 p2177 p2619 p3093 p3146 p3309 p3609 : Prop)
    (h112001 : p2619 ∨ p3609 ∨ (¬ p3146) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p2177) ∨ (¬ p3309))
    (h111852 : (¬ p2619) ∨ p3609 ∨ (¬ p3146))
    : p3609 ∨ (¬ p3146) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p2177) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2619 := (Or.elim h112001 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h111852 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116820 (p2132 p2241 p2264 p2619 p2996 p3146 p3609 : Prop)
    (h112002 : p2619 ∨ p3609 ∨ (¬ p3146) ∨ p2132 ∨ (¬ p2264) ∨ p2996 ∨ (¬ p2241))
    (h111852 : (¬ p2619) ∨ p3609 ∨ (¬ p3146))
    : p3609 ∨ (¬ p3146) ∨ p2132 ∨ (¬ p2264) ∨ p2996 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2619 := (Or.elim h112002 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h111852 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116821 (p2132 p2619 p2911 p2922 p3146 p3379 p3609 : Prop)
    (h112004 : p2619 ∨ (¬ p3146) ∨ (¬ p3379) ∨ p2132 ∨ (¬ p2911) ∨ (¬ p2922) ∨ p3609)
    (h111852 : (¬ p2619) ∨ p3609 ∨ (¬ p3146))
    : (¬ p3146) ∨ (¬ p3379) ∨ p2132 ∨ (¬ p2911) ∨ (¬ p2922) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2619 := (Or.elim h112004 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h111852 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116824 (p2352 p2459 p2651 p3016 p3073 p3399 p3527 : Prop)
    (h112267 : p3527 ∨ (¬ p3016) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p3399 ∨ p3073 ∨ (¬ p2651))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : (¬ p3016) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p3399 ∨ p3073 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3527 := (Or.elim h112267 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116826 (p2177 p2946 p3093 p3146 p3156 p3256 p3309 : Prop)
    (h112548 : (¬ p3156) ∨ p3309 ∨ (¬ p3256) ∨ p3146 ∨ p3093 ∨ (¬ p2946) ∨ p2177)
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p3309 ∨ (¬ p3256) ∨ p3146 ∨ p3093 ∨ (¬ p2946) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3156) := (Or.elim h112548 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116835 (p2088 p2459 p3005 p3083 p3286 p3755 p4438 : Prop)
    (h113772 : p3083 ∨ p3286 ∨ (¬ p2088) ∨ (¬ p3755) ∨ p2459 ∨ (¬ p4438) ∨ p3005)
    (h106140 : p4438 ∨ (¬ p2088))
    : p3083 ∨ p3286 ∨ (¬ p2088) ∨ (¬ p3755) ∨ p2459 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4438) := (Or.elim h113772 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h106140 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step116836 (p2264 p2274 p2307 p2396 p2449 p3204 p3319 : Prop)
    (h113829 : (¬ p2396) ∨ p2449 ∨ (¬ p2264) ∨ p2307 ∨ (¬ p2274) ∨ (¬ p3319) ∨ (¬ p3204))
    (h76204 : p2449 ∨ (¬ p2396) ∨ (¬ p2264) ∨ (¬ p2307))
    : (¬ p2396) ∨ p2449 ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p3319) ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2307 := (Or.elim h113829 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h76204 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step116841 (p2264 p2352 p2459 p2493 p2807 p3256 p3379 : Prop)
    (h115301 : (¬ p2264) ∨ p2352 ∨ p2459 ∨ p2493 ∨ p3379 ∨ (¬ p2807) ∨ (¬ p3256))
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2352 ∨ p2459 ∨ p2493 ∨ p3379 ∨ (¬ p2807) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2264) := (Or.elim h115301 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step116843 (p2264 p2459 p2608 p2807 p2819 p2829 p3256 : Prop)
    (h115305 : (¬ p2264) ∨ (¬ p3256) ∨ p2819 ∨ (¬ p2807) ∨ p2459 ∨ p2608 ∨ p2829)
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : (¬ p3256) ∨ p2819 ∨ (¬ p2807) ∨ p2459 ∨ p2608 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2264) := (Or.elim h115305 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116853 (p2459 p2470 p2528 p2946 p3005 p3136 p4041 p4236 : Prop)
    (h107584 : (¬ p2470) ∨ p2946 ∨ (¬ p4236) ∨ (¬ p2528) ∨ p2459 ∨ p3005 ∨ (¬ p4041) ∨ (¬ p3136))
    (h106488 : p4041 ∨ p2459)
    : p2459 ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p3136) ∨ p2946 ∨ (¬ p4236) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4041) := (Or.elim h107584 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u3))))))))))))))));
    (Or.elim h106488 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step116855 (p2331 p2459 p2470 p2528 p2797 p3005 p4041 p4236 : Prop)
    (h107596 : (¬ p2470) ∨ (¬ p2797) ∨ p2331 ∨ p3005 ∨ p2459 ∨ (¬ p4236) ∨ (¬ p4041) ∨ (¬ p2528))
    (h106488 : p4041 ∨ p2459)
    : (¬ p2797) ∨ p2459 ∨ (¬ p2528) ∨ (¬ p2470) ∨ p2331 ∨ p3005 ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4041) := (Or.elim h107596 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h106488 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step116858 (p2440 p2459 p2532 p2563 p2651 p3146 p3256 p3266 : Prop)
    (h107610 : (¬ p3256) ∨ p2563 ∨ (¬ p2440) ∨ (¬ p2532) ∨ p2651 ∨ (¬ p3146) ∨ p2459 ∨ p3266)
    (h96310 : p2532 ∨ (¬ p3146))
    : (¬ p3256) ∨ p2563 ∨ (¬ p3146) ∨ p2459 ∨ (¬ p2440) ∨ p3266 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2532) := (Or.elim h107610 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h96310 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step116862 (p2156 p2241 p2727 p3125 p3276 p3461 p3892 p4521 : Prop)
    (h109276 : p3276 ∨ (¬ p3892) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2241 ∨ p2727 ∨ (¬ p4521))
    (h108910 : (¬ p3276) ∨ (¬ p3461) ∨ (¬ p3125) ∨ (¬ p2156) ∨ p2241 ∨ p2727 ∨ (¬ p3892) ∨ (¬ p4521))
    : (¬ p3892) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2241 ∨ p2727 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3892 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3276 := (Or.elim h109276 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h108910 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step116865 (p2331 p2363 p2668 p3193 p3276 p3379 p3707 p4332 : Prop)
    (h109391 : p3193 ∨ p2363 ∨ (¬ p4332) ∨ p2668 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p3379) ∨ p2331)
    (h110334 : (¬ p3193) ∨ p3276 ∨ (¬ p3707))
    : p2363 ∨ (¬ p4332) ∨ p2668 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p3379) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3193 := (Or.elim h109391 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h110334 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116867 (p2210 p2417 p2598 p2972 p3201 p3707 p4322 p4395 : Prop)
    (h109573 : (¬ p2972) ∨ (¬ p4395) ∨ (¬ p2210) ∨ p2417 ∨ p3201 ∨ (¬ p4322) ∨ (¬ p3707) ∨ p2598)
    (h110190 : p2972 ∨ (¬ p3707) ∨ (¬ p4322))
    : (¬ p4395) ∨ (¬ p2210) ∨ p2417 ∨ p3201 ∨ (¬ p4322) ∨ (¬ p3707) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4395 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2972) := (Or.elim h109573 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h110190 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116870 (p2122 p2753 p2774 p3193 p3276 p3379 p3791 p3830 : Prop)
    (h110353 : (¬ p3193) ∨ (¬ p3791) ∨ p3276 ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2753) ∨ p3830)
    (h109384 : p3193 ∨ p3830 ∨ (¬ p3379))
    : (¬ p3791) ∨ p3276 ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2753) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3193) := (Or.elim h110353 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h109384 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step116872 (p2528 p2598 p2761 p3399 p3631 p3641 p3707 p3950 : Prop)
    (h110622 : (¬ p3631) ∨ p2761 ∨ (¬ p3707) ∨ (¬ p3399) ∨ p2598 ∨ p2528 ∨ p3641 ∨ (¬ p3950))
    (h106489 : p3950 ∨ (¬ p3399))
    : (¬ p3631) ∨ p2761 ∨ (¬ p3707) ∨ (¬ p3399) ∨ p2598 ∨ p2528 ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3950) := (Or.elim h110622 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step116878 (p2187 p2274 p2307 p2528 p2598 p2781 p3609 p3641 : Prop)
    (h111491 : p3641 ∨ (¬ p2187) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p2781))
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p2187) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3641 := (Or.elim h111491 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116879 (p2210 p2528 p2598 p2881 p2891 p3609 p3641 p4438 : Prop)
    (h111492 : p3641 ∨ (¬ p2881) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4438))
    (h106114 : p4438 ∨ (¬ p2528))
    : p3641 ∨ (¬ p2881) ∨ p3609 ∨ p2598 ∨ (¬ p2528) ∨ (¬ p2210) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4438) := (Or.elim h111492 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h106114 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step116880 (p2187 p2210 p2528 p3093 p3367 p3609 p3641 p4516 : Prop)
    (h111495 : p3641 ∨ (¬ p2187) ∨ p3609 ∨ (¬ p2528) ∨ p2210 ∨ (¬ p3093) ∨ (¬ p4516) ∨ p3367)
    (h111121 : (¬ p3641) ∨ (¬ p2528) ∨ p3609)
    : (¬ p2187) ∨ p3609 ∨ (¬ p2528) ∨ p2210 ∨ (¬ p3093) ∨ (¬ p4516) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3641 := (Or.elim h111495 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h111121 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step116884 (p2264 p2363 p2696 p2742 p2819 p2829 p2996 p3609 : Prop)
    (h111570 : p2819 ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2264) ∨ p2996 ∨ p2829 ∨ p3609 ∨ (¬ p2742))
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2264) ∨ p2996 ∨ p2829 ∨ p3609 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2819 := (Or.elim h111570 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116885 (p2166 p2210 p2241 p2363 p2774 p2819 p3366 p3609 : Prop)
    (h111572 : p2819 ∨ (¬ p2166) ∨ p2241 ∨ (¬ p3366) ∨ (¬ p2210) ∨ p2774 ∨ (¬ p2363) ∨ p3609)
    (h110442 : (¬ p2819) ∨ p3609 ∨ (¬ p2363))
    : (¬ p2166) ∨ p2241 ∨ (¬ p3366) ∨ (¬ p2210) ∨ p2774 ∨ (¬ p2363) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2819 := (Or.elim h111572 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h110442 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step116887 (p2132 p2331 p2619 p3266 p3323 p3461 p3506 p5568 : Prop)
    (h111955 : (¬ p3323) ∨ (¬ p3266) ∨ (¬ p2331) ∨ p3461 ∨ p2619 ∨ (¬ p3506) ∨ (¬ p5568) ∨ p2132)
    (h111949 : (¬ p3323) ∨ p3266 ∨ (¬ p5568) ∨ (¬ p3506) ∨ p2132 ∨ (¬ p2331) ∨ p2619)
    : (¬ p3323) ∨ (¬ p2331) ∨ p3461 ∨ p2619 ∨ (¬ p3506) ∨ (¬ p5568) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3266) := (Or.elim h111955 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h111949 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (u3 r5)))))))))))))))

theorem step116888 (p2331 p2717 p3266 p3323 p3425 p3461 p3506 p5558 : Prop)
    (h111956 : (¬ p3323) ∨ (¬ p3266) ∨ p3461 ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p5558))
    (h111950 : (¬ p3323) ∨ p3266 ∨ (¬ p5558) ∨ (¬ p3506) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331))
    : (¬ p3323) ∨ p3461 ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3266) := (Or.elim h111956 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h111950 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step116891 (p2459 p2668 p2737 p2797 p3073 p3425 p3527 p3576 : Prop)
    (h112265 : p3527 ∨ p3073 ∨ (¬ p3576) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p3425) ∨ (¬ p2737) ∨ (¬ p2459))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : p3073 ∨ (¬ p3576) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p3425) ∨ (¬ p2737) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3527 := (Or.elim h112265 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u6)))))))

theorem step116895 (p2122 p2177 p2253 p2774 p2946 p3146 p3156 p3256 : Prop)
    (h112553 : (¬ p3156) ∨ p2122 ∨ p2177 ∨ p3146 ∨ p2774 ∨ (¬ p3256) ∨ (¬ p2253) ∨ (¬ p2946))
    (h112559 : p3156 ∨ p3146 ∨ (¬ p3256))
    : p2122 ∨ p2177 ∨ p3146 ∨ p2774 ∨ (¬ p3256) ∨ (¬ p2253) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3156) := (Or.elim h112553 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h112559 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116901 (p2156 p2177 p2253 p2264 p2274 p2651 p2727 p3189 : Prop)
    (h112922 : p2264 ∨ p2274 ∨ (¬ p3189) ∨ p2177 ∨ (¬ p2253) ∨ p2156 ∨ (¬ p2651) ∨ p2727)
    (h112196 : (¬ p2264) ∨ (¬ p3189) ∨ p2177 ∨ (¬ p2651) ∨ p2727)
    : p2274 ∨ (¬ p3189) ∨ p2177 ∨ (¬ p2253) ∨ p2156 ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2264 := (Or.elim h112922 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h112196 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (u6 r3)))))))))))

theorem step116905 (p2598 p3166 p3201 p3256 p3266 p3361 p3425 p3868 : Prop)
    (h113484 : (¬ p3201) ∨ (¬ p3868) ∨ p3425 ∨ p3256 ∨ p3166 ∨ p2598 ∨ (¬ p3361) ∨ p3266)
    (h111391 : p3201 ∨ p3425 ∨ p2598)
    : (¬ p3868) ∨ p3425 ∨ p3256 ∨ p3166 ∨ p2598 ∨ (¬ p3361) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3201) := (Or.elim h113484 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h111391 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step116906 (p2122 p2132 p2274 p2470 p2860 p3016 p3083 p3589 : Prop)
    (h113545 : (¬ p2860) ∨ p2470 ∨ (¬ p2122) ∨ p2274 ∨ p3016 ∨ (¬ p2132) ∨ (¬ p3083) ∨ (¬ p3589))
    (h113138 : p2860 ∨ p2274 ∨ (¬ p2122))
    : p2470 ∨ (¬ p2122) ∨ p2274 ∨ p3016 ∨ (¬ p2132) ∨ (¬ p3083) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2860) := (Or.elim h113545 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h113138 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116909 (p2264 p2396 p2459 p2553 p2573 p3073 p3256 p3449 : Prop)
    (h114213 : (¬ p2459) ∨ p2264 ∨ p2553 ∨ (¬ p3073) ∨ p2573 ∨ p3256 ∨ (¬ p3449) ∨ p2396)
    (h112187 : (¬ p2264) ∨ p3256 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2553 ∨ (¬ p3073) ∨ p2573 ∨ p3256 ∨ (¬ p3449) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2264 := (Or.elim h114213 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h112187 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116914 (p2187 p2192 p2264 p2459 p2946 p2996 p3256 p4282 : Prop)
    (h115314 : (¬ p2264) ∨ p2192 ∨ (¬ p3256) ∨ p2187 ∨ p2946 ∨ p2459 ∨ p2996 ∨ (¬ p4282))
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2192 ∨ (¬ p3256) ∨ p2187 ∨ p2946 ∨ p2459 ∨ p2996 ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2264) := (Or.elim h115314 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116917 (p2132 p2341 p2459 p2860 p3266 p5197 p5250 p5442 : Prop)
    (h115741 : p5442 ∨ p3266 ∨ p2341 ∨ p2459 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p5197) ∨ (¬ p5250))
    (h106520 : p5250 ∨ p3266)
    : p5442 ∨ p3266 ∨ p2341 ∨ p2459 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5250) := (Or.elim h115741 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step116918 (p2284 p2341 p2459 p2946 p3266 p3461 p4850 p5442 : Prop)
    (h115789 : (¬ p5442) ∨ (¬ p3461) ∨ p2284 ∨ (¬ p2341) ∨ p2946 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4850))
    (h115787 : (¬ p5442) ∨ p3461 ∨ (¬ p3266) ∨ (¬ p4850) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2284 ∨ p2946)
    : (¬ p5442) ∨ p2284 ∨ (¬ p2341) ∨ p2946 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3461) := (Or.elim h115789 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h115787 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step116921 (p2352 p2406 p2440 p2553 p2922 p3564 p4079 p4620 p4710 : Prop)
    (h107666 : (¬ p2352) ∨ p3564 ∨ p2406 ∨ p2440 ∨ (¬ p4620) ∨ (¬ p2922) ∨ (¬ p4079) ∨ (¬ p2553) ∨ (¬ p4710))
    (h94484 : p4710 ∨ (¬ p2553))
    : (¬ p2352) ∨ (¬ p2922) ∨ p2440 ∨ (¬ p2553) ∨ p2406 ∨ p3564 ∨ (¬ p4079) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4710) := (Or.elim h107666 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => r7))))))))))))))));
    (Or.elim h94484 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step116922 (p2210 p2341 p2427 p2608 p3369 p3379 p3389 p4108 p5206 : Prop)
    (h107667 : (¬ p2608) ∨ p3379 ∨ p3389 ∨ p2210 ∨ (¬ p3369) ∨ (¬ p4108) ∨ p2341 ∨ (¬ p2427) ∨ (¬ p5206))
    (h96464 : p3369 ∨ p2210)
    : (¬ p5206) ∨ (¬ p2427) ∨ p2210 ∨ p3389 ∨ p2341 ∨ (¬ p4108) ∨ (¬ p2608) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5206 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3369) := (Or.elim h107667 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u0))))))))))))))))));
    (Or.elim h96464 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step116932 (p2192 p2761 p2946 p2996 p3125 p3412 p3516 p3773 p4155 : Prop)
    (h109454 : p3516 ∨ (¬ p2996) ∨ (¬ p3773) ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p4155) ∨ (¬ p2761) ∨ (¬ p3412))
    (h109544 : (¬ p3516) ∨ (¬ p2761) ∨ (¬ p3773))
    : (¬ p2996) ∨ (¬ p3773) ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p4155) ∨ (¬ p2761) ∨ (¬ p3412) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3516 := (Or.elim h109454 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h109544 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116936 (p2098 p2774 p2819 p2946 p3146 p3156 p3361 p3979 p4842 : Prop)
    (h110466 : (¬ p2819) ∨ p3156 ∨ p3146 ∨ p2946 ∨ p2774 ∨ (¬ p2098) ∨ (¬ p3361) ∨ (¬ p3979) ∨ (¬ p4842))
    (h111540 : p2819 ∨ (¬ p2098) ∨ p2774)
    : p3156 ∨ p3146 ∨ p2946 ∨ p2774 ∨ (¬ p2098) ∨ (¬ p3361) ∨ (¬ p3979) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2819) := (Or.elim h110466 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h111540 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step116950 (p2230 p2440 p2608 p2655 p2982 p3343 p3537 p3609 p5059 : Prop)
    (h111247 : p2982 ∨ (¬ p3609) ∨ (¬ p3537) ∨ p2440 ∨ (¬ p2608) ∨ p2230 ∨ p3343 ∨ (¬ p2655) ∨ (¬ p5059))
    (h109996 : (¬ p2982) ∨ p3343 ∨ p2440)
    : (¬ p3609) ∨ (¬ p3537) ∨ p2440 ∨ (¬ p2608) ∨ p2230 ∨ p3343 ∨ (¬ p2655) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2982 := (Or.elim h111247 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h109996 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step116952 (p2156 p2417 p2608 p2707 p3125 p3461 p3680 p4106 p4521 : Prop)
    (h111460 : (¬ p3125) ∨ (¬ p3680) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3461 ∨ p2417 ∨ (¬ p4106) ∨ p2608)
    (h112415 : p3125 ∨ p3461 ∨ (¬ p3680))
    : (¬ p3680) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3461 ∨ p2417 ∨ (¬ p4106) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3125) := (Or.elim h111460 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h112415 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step116954 (p2156 p2177 p2274 p2528 p3367 p3370 p3609 p3641 p4438 : Prop)
    (h111494 : p3641 ∨ p3609 ∨ (¬ p3370) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2528) ∨ p3367 ∨ (¬ p2177) ∨ (¬ p4438))
    (h106125 : p4438 ∨ (¬ p2274))
    : p3641 ∨ p3609 ∨ (¬ p3370) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2528) ∨ p3367 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4438) := (Or.elim h111494 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h106125 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step116961 (p2230 p2373 p2459 p2656 p2727 p2807 p3037 p3073 p3527 : Prop)
    (h112275 : p3527 ∨ (¬ p2373) ∨ p2807 ∨ (¬ p2230) ∨ (¬ p2727) ∨ p3073 ∨ (¬ p2656) ∨ (¬ p3037) ∨ (¬ p2459))
    (h111023 : (¬ p3527) ∨ p3073 ∨ (¬ p2459))
    : (¬ p2373) ∨ p2807 ∨ (¬ p2230) ∨ (¬ p2727) ∨ p3073 ∨ (¬ p2656) ∨ (¬ p3037) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3527 := (Or.elim h112275 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h111023 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u7)))))))

theorem step116962 (p2136 p2156 p2860 p3105 p3125 p3166 p3256 p3266 p3506 : Prop)
    (h112454 : p3125 ∨ (¬ p3256) ∨ (¬ p3506) ∨ p3105 ∨ (¬ p3166) ∨ (¬ p2860) ∨ p3266 ∨ (¬ p2136) ∨ p2156)
    (h111430 : (¬ p3125) ∨ p3105 ∨ (¬ p2860))
    : (¬ p3256) ∨ (¬ p3506) ∨ p3105 ∨ (¬ p3166) ∨ (¬ p2860) ∨ p3266 ∨ (¬ p2136) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3125 := (Or.elim h112454 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h111430 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116968 (p2509 p2528 p2901 p2958 p3051 p3115 p3246 p3379 p3950 : Prop)
    (h112804 : (¬ p3246) ∨ (¬ p3051) ∨ (¬ p3950) ∨ p2901 ∨ p2528 ∨ (¬ p2958) ∨ p3379 ∨ (¬ p2509) ∨ (¬ p3115))
    (h111053 : p3246 ∨ p2901 ∨ (¬ p3115))
    : (¬ p3051) ∨ (¬ p3950) ∨ p2901 ∨ p2528 ∨ (¬ p2958) ∨ p3379 ∨ (¬ p2509) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3246) := (Or.elim h112804 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h111053 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u7)))))))

theorem step116969 (p2156 p2274 p2396 p2417 p2651 p3276 p3343 p4236 p5284 : Prop)
    (h112990 : (¬ p2417) ∨ p3343 ∨ (¬ p5284) ∨ (¬ p2156) ∨ p2651 ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3276) ∨ (¬ p4236))
    (h111255 : (¬ p3343) ∨ (¬ p3276) ∨ (¬ p5284))
    : (¬ p2417) ∨ (¬ p5284) ∨ (¬ p2156) ∨ p2651 ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3276) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3343 := (Or.elim h112990 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h111255 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116980 (p2132 p2417 p2619 p2922 p3146 p3366 p3379 p3399 p3950 : Prop)
    (h114288 : (¬ p2922) ∨ (¬ p2417) ∨ p2619 ∨ p3146 ∨ (¬ p3399) ∨ p3379 ∨ p2132 ∨ (¬ p3366) ∨ (¬ p3950))
    (h106489 : p3950 ∨ (¬ p3399))
    : (¬ p2922) ∨ (¬ p2417) ∨ p2619 ∨ p3146 ∨ (¬ p3399) ∨ p3379 ∨ p2132 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3950) := (Or.elim h114288 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step116981 (p2417 p2696 p2922 p3005 p3256 p3366 p3379 p3399 p3950 : Prop)
    (h114289 : (¬ p2922) ∨ (¬ p2417) ∨ p3256 ∨ (¬ p3399) ∨ (¬ p3950) ∨ p2696 ∨ p3005 ∨ (¬ p3366) ∨ p3379)
    (h106489 : p3950 ∨ (¬ p3399))
    : (¬ p2922) ∨ (¬ p2417) ∨ p3256 ∨ (¬ p3399) ∨ p2696 ∨ p3005 ∨ (¬ p3366) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3950) := (Or.elim h114289 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step116985 (p2088 p2363 p2383 p2641 p2651 p2911 p2922 p3487 p3567 : Prop)
    (h114656 : (¬ p2383) ∨ p2363 ∨ p2922 ∨ p2911 ∨ (¬ p2641) ∨ (¬ p2088) ∨ (¬ p3567) ∨ (¬ p3487) ∨ p2651)
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2363 ∨ p2922 ∨ p2911 ∨ (¬ p2641) ∨ (¬ p2088) ∨ (¬ p3567) ∨ (¬ p3487) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2383) := (Or.elim h114656 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step116988 (p2088 p2363 p2383 p2696 p2748 p2774 p2829 p2992 p3156 : Prop)
    (h114813 : p2774 ∨ (¬ p2383) ∨ (¬ p2088) ∨ p2992 ∨ p2363 ∨ (¬ p2829) ∨ (¬ p2748) ∨ p3156 ∨ p2696)
    (h114823 : p2383 ∨ p2363 ∨ (¬ p2088))
    : p2774 ∨ (¬ p2088) ∨ p2992 ∨ p2363 ∨ (¬ p2829) ∨ (¬ p2748) ∨ p3156 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2383) := (Or.elim h114813 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h114823 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step116990 (p2246 p2264 p2459 p2608 p2807 p2819 p2829 p3093 p3256 : Prop)
    (h115309 : (¬ p2264) ∨ p2829 ∨ p2819 ∨ (¬ p2807) ∨ p3093 ∨ (¬ p3256) ∨ (¬ p2608) ∨ (¬ p2246) ∨ p2459)
    (h112096 : p2264 ∨ p2459 ∨ (¬ p3256))
    : p2829 ∨ p2819 ∨ (¬ p2807) ∨ p3093 ∨ (¬ p3256) ∨ (¬ p2608) ∨ (¬ p2246) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2264) := (Or.elim h115309 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h112096 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step117005 (p2470 p3083 p3212 p3343 p3366 p3370 p3371 p3461 p3564 p3680 : Prop)
    (h109853 : (¬ p3564) ∨ p3461 ∨ (¬ p3083) ∨ (¬ p3680) ∨ p3343 ∨ (¬ p3366) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ p2470)
    (h116363 : p3461 ∨ (¬ p3680) ∨ p3564)
    : p3461 ∨ (¬ p3083) ∨ (¬ p3680) ∨ p3343 ∨ (¬ p3366) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3564) := (Or.elim h109853 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h116363 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u9 r1)))))))

theorem step117006 (p2241 p2753 p3093 p3201 p3323 p3333 p3362 p3389 p3564 p4319 : Prop)
    (h110050 : p3564 ∨ p3323 ∨ (¬ p2753) ∨ p3093 ∨ (¬ p3389) ∨ p3201 ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p2241) ∨ (¬ p4319))
    (h101186 : p3093 ∨ (¬ p4319) ∨ (¬ p2241) ∨ p3323 ∨ (¬ p3564))
    : p3323 ∨ (¬ p2753) ∨ p3093 ∨ (¬ p3389) ∨ p3201 ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p2241) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3564 := (Or.elim h110050 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h101186 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u9)))))))))))

theorem step117011 (p2145 p2449 p2685 p2807 p3266 p3755 p3950 p4032 p4117 p4322 : Prop)
    (h110680 : (¬ p2449) ∨ (¬ p4322) ∨ p2685 ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p4032) ∨ (¬ p4117) ∨ (¬ p3950) ∨ (¬ p2807) ∨ (¬ p2145))
    (h110901 : p2449 ∨ (¬ p3755) ∨ p2685)
    : (¬ p4322) ∨ p2685 ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p4032) ∨ (¬ p4117) ∨ (¬ p3950) ∨ (¬ p2807) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2449) := (Or.elim h110680 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h110901 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u1 r1)))))))

theorem step117012 (p2528 p2598 p2951 p2992 p3051 p3246 p3367 p3537 p3641 p3950 : Prop)
    (h110738 : p3641 ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p2992) ∨ p2598 ∨ p2528 ∨ p3537 ∨ (¬ p2951) ∨ (¬ p3950))
    (h110392 : (¬ p3641) ∨ p3537 ∨ (¬ p3367))
    : (¬ p3246) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p2992) ∨ p2598 ∨ p2528 ∨ p3537 ∨ (¬ p2951) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3641 := (Or.elim h110738 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h110392 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step117014 (p2951 p2992 p3005 p3051 p3073 p3246 p3266 p3707 p3950 p4288 : Prop)
    (h110766 : p3073 ∨ (¬ p4288) ∨ p3707 ∨ (¬ p3246) ∨ (¬ p3266) ∨ p3005 ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p3950))
    (h109786 : (¬ p3073) ∨ p3707 ∨ (¬ p3266))
    : (¬ p4288) ∨ p3707 ∨ (¬ p3246) ∨ (¬ p3266) ∨ p3005 ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4288 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3073 := (Or.elim h110766 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h109786 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step117016 (p2331 p2459 p2753 p2797 p2911 p3323 p3347 p3389 p3755 p4117 : Prop)
    (h110898 : (¬ p3323) ∨ (¬ p3755) ∨ (¬ p2331) ∨ p3389 ∨ p2797 ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p4117) ∨ p2911 ∨ p2459)
    (h110991 : p3323 ∨ (¬ p3755) ∨ p2797)
    : (¬ p3755) ∨ (¬ p2331) ∨ p3389 ∨ p2797 ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p4117) ∨ p2911 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3323) := (Or.elim h110898 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h110991 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step117017 (p2098 p2528 p2598 p2748 p2761 p2972 p3115 p3368 p3641 p5284 : Prop)
    (h111144 : (¬ p3641) ∨ (¬ p3115) ∨ (¬ p5284) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p2098) ∨ p2972 ∨ p2598 ∨ (¬ p2748) ∨ (¬ p3368))
    (h111465 : p3641 ∨ (¬ p2098) ∨ p2598)
    : (¬ p3115) ∨ (¬ p5284) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p2098) ∨ p2972 ∨ p2598 ∨ (¬ p2748) ∨ (¬ p3368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3641) := (Or.elim h111144 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h111465 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u6 r1)))))))

theorem step117018 (p2156 p2246 p2274 p2396 p2630 p2651 p2749 p3343 p3645 p3755 : Prop)
    (h111287 : (¬ p3343) ∨ (¬ p3755) ∨ (¬ p3645) ∨ p2156 ∨ p2630 ∨ p2396 ∨ p2274 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2749))
    (h109937 : p3343 ∨ (¬ p3755) ∨ p2630)
    : (¬ p3755) ∨ (¬ p3645) ∨ p2156 ∨ p2630 ∨ p2396 ∨ p2274 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3343) := (Or.elim h111287 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h109937 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step117025 (p2098 p2132 p2252 p2619 p2655 p2748 p2911 p3146 p3389 p5558 : Prop)
    (h111888 : (¬ p2619) ∨ p3389 ∨ (¬ p3146) ∨ p2911 ∨ (¬ p2098) ∨ (¬ p2655) ∨ (¬ p5558) ∨ p2132 ∨ (¬ p2252) ∨ (¬ p2748))
    (h111972 : p2619 ∨ (¬ p2098) ∨ p2132)
    : p3389 ∨ (¬ p3146) ∨ p2911 ∨ (¬ p2098) ∨ (¬ p2655) ∨ (¬ p5558) ∨ p2132 ∨ (¬ p2252) ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2619) := (Or.elim h111888 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h111972 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u6 r1)))))))

theorem step117036 (p2252 p2850 p2922 p2946 p3146 p3156 p3201 p3266 p3541 p4322 : Prop)
    (h113130 : p3146 ∨ (¬ p2922) ∨ (¬ p2850) ∨ p2946 ∨ p3156 ∨ p3201 ∨ (¬ p3266) ∨ (¬ p2252) ∨ (¬ p3541) ∨ (¬ p4322))
    (h79124 : p3146 ∨ p3266 ∨ p2946 ∨ p3156)
    : p3146 ∨ (¬ p2922) ∨ (¬ p2850) ∨ p2946 ∨ p3156 ∨ p3201 ∨ (¬ p2252) ∨ (¬ p3541) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3266) := (Or.elim h113130 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h79124 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step117039 (p2210 p2252 p2264 p2295 p2307 p2459 p2608 p2972 p3983 p4450 : Prop)
    (h113908 : (¬ p2295) ∨ p2264 ∨ p2307 ∨ (¬ p2210) ∨ p2459 ∨ p2608 ∨ (¬ p2252) ∨ (¬ p2972) ∨ (¬ p3983) ∨ (¬ p4450))
    (h106470 : p4450 ∨ (¬ p2972))
    : (¬ p2295) ∨ p2264 ∨ p2307 ∨ (¬ p2210) ∨ p2459 ∨ p2608 ∨ (¬ p2252) ∨ (¬ p2972) ∨ (¬ p3983) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4450) := (Or.elim h113908 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => r8))))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u7)))))

theorem step117046 (p2230 p2241 p2753 p2850 p3105 p3362 p3449 p3680 p5123 p5693 : Prop)
    (h115145 : p2850 ∨ (¬ p3680) ∨ p3449 ∨ (¬ p2230) ∨ (¬ p5123) ∨ (¬ p3105) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p5693) ∨ (¬ p2241))
    (h106200 : p5123 ∨ (¬ p2241))
    : p2850 ∨ (¬ p3680) ∨ p3449 ∨ (¬ p2230) ∨ (¬ p3105) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p5693) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5123) := (Or.elim h115145 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106200 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u8)))))

theorem step117047 (p2246 p2341 p2459 p2651 p3016 p3266 p3366 p3820 p5250 p6134 : Prop)
    (h115578 : p6134 ∨ (¬ p2246) ∨ p2341 ∨ (¬ p3016) ∨ (¬ p2651) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3366) ∨ (¬ p3820) ∨ p2459)
    (h106520 : p5250 ∨ p3266)
    : p6134 ∨ (¬ p2246) ∨ p2341 ∨ (¬ p3016) ∨ (¬ p2651) ∨ p3266 ∨ (¬ p3366) ∨ (¬ p3820) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5250) := (Or.elim h115578 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step117048 (p2220 p2246 p2651 p2749 p3016 p3146 p3266 p3645 p5250 p6134 : Prop)
    (h115579 : p6134 ∨ p3146 ∨ (¬ p3016) ∨ p3266 ∨ p2220 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3645) ∨ (¬ p5250))
    (h106520 : p5250 ∨ p3266)
    : p6134 ∨ p3146 ∨ (¬ p3016) ∨ p3266 ∨ p2220 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5250) := (Or.elim h115579 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => r8))))))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step117050 (p2230 p2241 p2860 p3366 p3461 p3695 p3707 p3830 p3905 p5442 : Prop)
    (h115813 : (¬ p5442) ∨ (¬ p3461) ∨ p2860 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2230 ∨ p2241)
    (h100402 : (¬ p3707) ∨ p2241 ∨ p3461 ∨ (¬ p3830))
    : (¬ p5442) ∨ p2860 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2230 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3461) := (Or.elim h115813 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h100402 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step117057 (p2177 p2311 p2341 p2641 p2651 p2667 p3193 p3276 p3707 p4116 p4635 : Prop)
    (h109395 : p3193 ∨ p3276 ∨ p2341 ∨ p2641 ∨ (¬ p4635) ∨ (¬ p3707) ∨ (¬ p2667) ∨ (¬ p2651) ∨ (¬ p2177) ∨ (¬ p4116) ∨ (¬ p2311))
    (h110334 : (¬ p3193) ∨ p3276 ∨ (¬ p3707))
    : p3276 ∨ p2341 ∨ p2641 ∨ (¬ p4635) ∨ (¬ p3707) ∨ (¬ p2667) ∨ (¬ p2651) ∨ (¬ p2177) ∨ (¬ p4116) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3193 := (Or.elim h109395 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h110334 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step117058 (p2246 p2352 p2363 p2573 p2749 p2946 p3115 p3347 p3506 p4322 p4450 : Prop)
    (h109652 : (¬ p3115) ∨ p2573 ∨ (¬ p3506) ∨ p2352 ∨ p2363 ∨ (¬ p2946) ∨ (¬ p4322) ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) ∨ (¬ p4450))
    (h106564 : p4450 ∨ (¬ p3115))
    : (¬ p3115) ∨ p2573 ∨ (¬ p3506) ∨ p2352 ∨ p2363 ∨ (¬ p2946) ∨ (¬ p4322) ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4450) := (Or.elim h109652 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => r9))))))))))))))))))));
    (Or.elim h106564 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117059 (p2144 p2252 p2437 p2655 p3212 p3343 p3366 p3389 p3461 p3564 p3680 : Prop)
    (h109856 : (¬ p3564) ∨ p3343 ∨ (¬ p2437) ∨ p3461 ∨ (¬ p3680) ∨ (¬ p3212) ∨ (¬ p2655) ∨ (¬ p2144) ∨ (¬ p2252) ∨ p3366 ∨ p3389)
    (h116363 : p3461 ∨ (¬ p3680) ∨ p3564)
    : p3343 ∨ (¬ p2437) ∨ p3461 ∨ (¬ p3680) ∨ (¬ p3212) ∨ (¬ p2655) ∨ (¬ p2144) ∨ (¬ p2252) ∨ p3366 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3366) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3564) := (Or.elim h109856 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (False.elim (u9 r9))))))))))))))))))))));
    (Or.elim h116363 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u10 r1)))))))

theorem step117066 (p2246 p2352 p2363 p2573 p2749 p2946 p3115 p3136 p3347 p3755 p4450 : Prop)
    (h110866 : (¬ p3115) ∨ (¬ p3755) ∨ p2363 ∨ (¬ p2946) ∨ p2352 ∨ p2573 ∨ p3136 ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) ∨ (¬ p4450))
    (h109505 : p3115 ∨ (¬ p3755) ∨ p3136)
    : (¬ p3755) ∨ p2363 ∨ (¬ p2946) ∨ p2352 ∨ p2573 ∨ p3136 ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3115) := (Or.elim h110866 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h109505 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u5 r1)))))))

theorem step117078 (p2187 p2192 p2210 p2246 p2264 p2363 p2651 p2911 p2992 p3093 p3580 : Prop)
    (h113309 : p2192 ∨ (¬ p2992) ∨ p2363 ∨ p2911 ∨ (¬ p2210) ∨ p2187 ∨ p3093 ∨ (¬ p2264) ∨ (¬ p2246) ∨ (¬ p3580) ∨ (¬ p2651))
    (h75461 : p2363 ∨ p2210 ∨ p2187 ∨ p2192)
    : p2192 ∨ (¬ p2992) ∨ p2363 ∨ p2911 ∨ p2187 ∨ p3093 ∨ (¬ p2264) ∨ (¬ p2246) ∨ (¬ p3580) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2210) := (Or.elim h113309 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h75461 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step117082 (p2396 p2651 p2727 p2996 p3266 p3286 p3343 p3461 p3631 p4450 p4952 : Prop)
    (h113840 : (¬ p2396) ∨ (¬ p3343) ∨ p2996 ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p4952) ∨ (¬ p4450))
    (h109938 : p3343 ∨ (¬ p3286) ∨ p2651)
    : (¬ p2396) ∨ p2996 ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p4952) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3343) := (Or.elim h113840 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h109938 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (u3 r1)))))))

theorem step117091 (p2122 p2177 p2210 p2241 p2307 p2459 p2881 p2891 p2972 p3093 p3146 p4870 : Prop)
    (h107723 : p3146 ∨ (¬ p2210) ∨ (¬ p4870) ∨ (¬ p2891) ∨ p2177 ∨ p2881 ∨ (¬ p3093) ∨ p2307 ∨ p2459 ∨ p2122 ∨ (¬ p2972) ∨ p2241)
    (h80800 : p2241 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p2881))
    : (¬ p3093) ∨ p2241 ∨ p3146 ∨ p2307 ∨ (¬ p2210) ∨ p2459 ∨ (¬ p2891) ∨ p2122 ∨ p2177 ∨ (¬ p2972) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2881 := (Or.elim h107723 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u7 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (u1 r10))))))))))))))))))))))));
    (Or.elim h80800 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u11)))))))))

theorem step117111 (p2295 p2363 p2383 p2563 p2598 p2668 p2781 p2850 p2870 p3201 p3987 p4138 p5045 p5059 : Prop)
    (h107742 : (¬ p4138) ∨ p2598 ∨ (¬ p2870) ∨ p2850 ∨ p2668 ∨ p3201 ∨ (¬ p2383) ∨ (¬ p5045) ∨ (¬ p2295) ∨ p2563 ∨ (¬ p3987) ∨ (¬ p2781) ∨ (¬ p5059) ∨ (¬ p2363))
    (h106331 : p2781 ∨ (¬ p3987))
    : (¬ p2363) ∨ p2850 ∨ p2598 ∨ p2563 ∨ (¬ p2295) ∨ (¬ p2383) ∨ p3201 ∨ p2668 ∨ (¬ p2870) ∨ (¬ p4138) ∨ (¬ p5059) ∨ (¬ p3987) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2781) := (Or.elim h107742 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => q11) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u10))) (fun r12 => (False.elim (r12 u0))))))))))))))))))))))))))));
    (Or.elim h106331 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u11)))))

theorem step117128 (p5500 p5503 p6130 : Prop)
    (h9583 : (¬ p5500) ∨ p5503)
    (h116279 : p6130 ∨ p5500)
    : p6130 ∨ p5503 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5503) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5500) := (Or.elim h9583 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h116279 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step117129 (p2437 p2440 p3434 p4253 p5500 p6130 : Prop)
    (h109361 : (¬ p5500) ∨ (¬ p4253) ∨ p2440 ∨ p3434 ∨ p2437)
    (h116279 : p6130 ∨ p5500)
    : p6130 ∨ (¬ p4253) ∨ p3434 ∨ p2440 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5500) := (Or.elim h109361 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h116279 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step117135 (p5500 p6130 p6131 : Prop)
    (h116278 : (¬ p5500) ∨ (¬ p6130))
    (h116265 : p5500 ∨ (¬ p6131))
    : (¬ p6131) ∨ (¬ p6130) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6131 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6130 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5500) := (Or.elim h116278 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h116265 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117136 (p5503 p6130 p6131 : Prop)
    (h117128 : p6130 ∨ p5503)
    (h117135 : (¬ p6131) ∨ (¬ p6130))
    : (¬ p6131) ∨ p5503 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6131 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5503) := (fun h => hn (Or.inr h));
    let u2 : p6130 := (Or.elim h117128 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h117135 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step117137 (p2437 p2440 p3434 p4253 p6130 p6131 : Prop)
    (h117129 : p6130 ∨ (¬ p4253) ∨ p3434 ∨ p2440 ∨ p2437)
    (h117135 : (¬ p6131) ∨ (¬ p6130))
    : (¬ p6131) ∨ (¬ p4253) ∨ p3434 ∨ p2440 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6131 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p6130 := (Or.elim h117129 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h117135 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u5)))))

theorem step117143 (p4207 p5092 p6008 : Prop)
    (h116396 : p6008 ∨ (¬ p4207) ∨ p5092)
    (h13041 : p4207 ∨ p6008)
    : p5092 ∨ p6008 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6008) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4207) := (Or.elim h116396 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u0 r1))))));
    (Or.elim h13041 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step117144 (p4380 p5092 p6008 : Prop)
    (h116295 : (¬ p5092) ∨ (¬ p6008))
    (h108691 : p5092 ∨ p4380)
    : p4380 ∨ (¬ p6008) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4380) := (fun h => hn (Or.inl h));
    let u1 : p6008 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h116295 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108691 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117145 (p4323 p5092 p6008 : Prop)
    (h116295 : (¬ p5092) ∨ (¬ p6008))
    (h108692 : p5092 ∨ p4323)
    : p4323 ∨ (¬ p6008) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4323) := (fun h => hn (Or.inl h));
    let u1 : p6008 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h116295 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108692 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117146 (p4032 p5092 p6008 : Prop)
    (h116295 : (¬ p5092) ∨ (¬ p6008))
    (h108693 : p5092 ∨ p4032)
    : p4032 ∨ (¬ p6008) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4032) := (fun h => hn (Or.inl h));
    let u1 : p6008 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h116295 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108693 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117147 (p3212 p5092 p6008 : Prop)
    (h8577 : p3212 ∨ (¬ p5092))
    (h117143 : p5092 ∨ p6008)
    : p6008 ∨ p3212 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3212) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h8577 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117143 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117148 (p4209 p5092 p6008 : Prop)
    (h8575 : p4209 ∨ (¬ p5092))
    (h117143 : p5092 ∨ p6008)
    : p6008 ∨ p4209 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4209) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h8575 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117143 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117149 (p4207 p5092 p6008 : Prop)
    (h8576 : p4207 ∨ (¬ p5092))
    (h117143 : p5092 ∨ p6008)
    : p6008 ∨ p4207 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4207) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5092) := (Or.elim h8576 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117143 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117151 (p3051 p4192 p4323 p4380 p6008 : Prop)
    (h17330 : (¬ p3051) ∨ (¬ p4192) ∨ (¬ p4323) ∨ (¬ p4380))
    (h117144 : p4380 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p4192) ∨ (¬ p4323) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4380) := (Or.elim h17330 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h117144 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117152 (p2220 p2533 p4323 p4380 p6008 : Prop)
    (h13033 : (¬ p2220) ∨ (¬ p2533) ∨ (¬ p4323) ∨ (¬ p4380))
    (h117144 : p4380 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p2533) ∨ (¬ p4323) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4380) := (Or.elim h13033 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h117144 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117153 (p2982 p4031 p4323 p4380 p6008 : Prop)
    (h17886 : (¬ p2982) ∨ (¬ p4031) ∨ (¬ p4323) ∨ (¬ p4380))
    (h117144 : p4380 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p4031) ∨ (¬ p4323) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4380) := (Or.elim h17886 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h117144 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117157 (p2373 p2533 p3680 p3773 p4380 p4533 p6008 : Prop)
    (h105394 : p4533)
    (h60681 : (¬ p2373) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p4533))
    (h117144 : p4380 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p2373) ∨ (¬ p2533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4533 := h105394;
    let u6 : (¬ p4380) := (Or.elim h60681 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h117144 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117165 (p2255 p2417 p2651 p2922 p2957 p2992 p3680 p3773 p3951 p4116 p4380 p6008 : Prop)
    (h105367 : p2255)
    (h106536 : p3951)
    (h96724 : (¬ p4116) ∨ p2992 ∨ (¬ p2651) ∨ (¬ p3680) ∨ (¬ p2922) ∨ (¬ p2255) ∨ (¬ p3951) ∨ (¬ p2417) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p2957))
    (h117144 : p4380 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p2417) ∨ (¬ p3680) ∨ (¬ p2922) ∨ (¬ p2651) ∨ p2992 ∨ (¬ p2957) ∨ (¬ p4116) ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    let u10 : p3951 := h106536;
    let u11 : (¬ p4380) := (Or.elim h96724 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h117144 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117166 (p2098 p2774 p2819 p4861 : Prop)
    (h101502 : (¬ p4861) ∨ p2098 ∨ (¬ p2774))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p2098 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4861) := (Or.elim h101502 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96379 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117167 (p2819 p2829 p3537 p4861 : Prop)
    (h102037 : p3537 ∨ (¬ p4861) ∨ (¬ p2829))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p3537 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4861) := (Or.elim h102037 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96379 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117168 (p2819 p2860 p4744 p4861 : Prop)
    (h113493 : (¬ p2860) ∨ p4744 ∨ (¬ p4861))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p4744 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4744) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4861) := (Or.elim h113493 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96379 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117170 (p2122 p2363 p2819 p3609 p4405 p4861 : Prop)
    (h105512 : p4405)
    (h75000 : (¬ p4861) ∨ p2122 ∨ (¬ p4405) ∨ p2363 ∨ (¬ p3609))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p2363 ∨ (¬ p3609) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4861) := (Or.elim h75000 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117172 (p2122 p2819 p4019 p4405 p4861 p5580 : Prop)
    (h105512 : p4405)
    (h97858 : (¬ p4019) ∨ (¬ p5580) ∨ (¬ p4405) ∨ (¬ p4861) ∨ p2122)
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p4019) ∨ (¬ p5580) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4861) := (Or.elim h97858 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117176 (p2528 p2819 p3083 p3609 p4375 p4753 p4861 : Prop)
    (h105514 : p4753)
    (h74990 : (¬ p4861) ∨ p2528 ∨ (¬ p4375) ∨ (¬ p4753) ∨ (¬ p3609) ∨ p3083)
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p2528 ∨ (¬ p3609) ∨ (¬ p4375) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4861) := (Or.elim h74990 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117184 (p2307 p2782 p2819 p3073 p3609 p3955 p4318 p4861 : Prop)
    (h75022 : (¬ p4318) ∨ p3073 ∨ p2307 ∨ (¬ p3955) ∨ (¬ p2782) ∨ (¬ p4861) ∨ (¬ p3609))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p4318) ∨ (¬ p2782) ∨ (¬ p3955) ∨ (¬ p3609) ∨ p3073 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4861) := (Or.elim h75022 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117187 (p2088 p2274 p2318 p2341 p2819 p3609 p4401 p4861 : Prop)
    (h115628 : p2341 ∨ (¬ p4861) ∨ (¬ p3609) ∨ p2274 ∨ (¬ p4401) ∨ p2088 ∨ (¬ p2318))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p2318) ∨ (¬ p4401) ∨ (¬ p3609) ∨ p2088 ∨ p2341 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4861) := (Or.elim h115628 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117195 (p2363 p2373 p2406 p2774 p2819 p3379 p3609 p4134 p4733 p4861 : Prop)
    (h105430 : p4733)
    (h105379 : p4134)
    (h74902 : (¬ p3609) ∨ p3379 ∨ (¬ p4134) ∨ (¬ p4733) ∨ p2373 ∨ p2406 ∨ p2363 ∨ (¬ p4861) ∨ (¬ p2774))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p3609) ∨ p3379 ∨ p2363 ∨ (¬ p2774) ∨ p2406 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : p4134 := h105379;
    let u9 : (¬ p4861) := (Or.elim h74902 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117196 (p2166 p2210 p2241 p2363 p2750 p2753 p2774 p2819 p3609 p4134 p4861 : Prop)
    (h106345 : p2750)
    (h105379 : p4134)
    (h74899 : (¬ p3609) ∨ p2363 ∨ (¬ p2774) ∨ (¬ p2241) ∨ (¬ p4134) ∨ (¬ p4861) ∨ (¬ p2753) ∨ (¬ p2750) ∨ p2210 ∨ p2166)
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ p2166 ∨ (¬ p2241) ∨ (¬ p2774) ∨ p2210 ∨ (¬ p2753) ∨ p2363 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4134 := h105379;
    let u10 : (¬ p4861) := (Or.elim h74899 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (u1 r8))))))))))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117197 (p2363 p2449 p2459 p2663 p2774 p2807 p2819 p3363 p3367 p3609 p4861 : Prop)
    (h114228 : (¬ p2459) ∨ (¬ p3609) ∨ (¬ p2774) ∨ p3367 ∨ p2807 ∨ p2363 ∨ p2449 ∨ (¬ p2663) ∨ (¬ p3363) ∨ (¬ p4861))
    (h96379 : p4861 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p3363) ∨ (¬ p2663) ∨ (¬ p3609) ∨ p2449 ∨ (¬ p2774) ∨ p2807 ∨ p3367 ∨ p2363 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4861) := (Or.elim h114228 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => r8))))))))))))))))));
    (Or.elim h96379 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117200 (p3453 p4370 p4683 p5866 : Prop)
    (h116458 : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453))
    (h12187 : p3453 ∨ p5866)
    : p4683 ∨ p5866 ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5866) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3453) := (Or.elim h116458 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h12187 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step117201 (p3051 p4192 p4323 p6008 : Prop)
    (h117151 : (¬ p6008) ∨ (¬ p4192) ∨ (¬ p4323) ∨ (¬ p3051))
    (h117145 : p4323 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p4192) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4323) := (Or.elim h117151 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h117145 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117202 (p2220 p2533 p4323 p6008 : Prop)
    (h117152 : (¬ p6008) ∨ (¬ p2533) ∨ (¬ p4323) ∨ (¬ p2220))
    (h117145 : p4323 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p2533) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4323) := (Or.elim h117152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h117145 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117203 (p2982 p4031 p4323 p6008 : Prop)
    (h117153 : (¬ p6008) ∨ (¬ p4031) ∨ (¬ p4323) ∨ (¬ p2982))
    (h117145 : p4323 ∨ (¬ p6008))
    : (¬ p6008) ∨ (¬ p4031) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6008 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4323) := (Or.elim h117153 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h117145 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117207 (p4370 p4683 p5866 : Prop)
    (h117200 : p4683 ∨ p5866 ∨ (¬ p4370))
    (h12191 : p4370 ∨ p5866)
    : p4683 ∨ p5866 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5866) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4370) := (Or.elim h117200 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h12191 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step117208 (p4683 p4687 p5866 : Prop)
    (h116296 : (¬ p4683) ∨ (¬ p5866))
    (h108950 : p4683 ∨ p4687)
    : p4687 ∨ (¬ p5866) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4687) := (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h116296 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108950 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117209 (p4683 p4688 p5866 : Prop)
    (h116296 : (¬ p4683) ∨ (¬ p5866))
    (h108951 : p4683 ∨ p4688)
    : p4688 ∨ (¬ p5866) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4688) := (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h116296 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108951 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117210 (p2518 p4683 p5866 : Prop)
    (h116296 : (¬ p4683) ∨ (¬ p5866))
    (h108952 : p4683 ∨ p2518)
    : p2518 ∨ (¬ p5866) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2518) := (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h116296 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108952 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117211 (p4683 p4690 p5866 : Prop)
    (h116296 : (¬ p4683) ∨ (¬ p5866))
    (h108953 : p4683 ∨ p4690)
    : p4690 ∨ (¬ p5866) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4690) := (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h116296 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108953 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117212 (p2509 p4683 p5866 : Prop)
    (h7550 : p2509 ∨ (¬ p4683))
    (h117207 : p4683 ∨ p5866)
    : p5866 ∨ p2509 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2509) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h7550 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117207 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117213 (p3453 p4683 p5866 : Prop)
    (h7548 : p3453 ∨ (¬ p4683))
    (h117207 : p4683 ∨ p5866)
    : p5866 ∨ p3453 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3453) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h7548 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117207 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117214 (p4370 p4683 p5866 : Prop)
    (h7549 : p4370 ∨ (¬ p4683))
    (h117207 : p4683 ∨ p5866)
    : p5866 ∨ p4370 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4370) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h7549 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h117207 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117215 (p4683 p4685 p5866 : Prop)
    (h7552 : (¬ p4683) ∨ p4685)
    (h117207 : p4683 ∨ p5866)
    : p5866 ∨ p4685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4685) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4683) := (Or.elim h7552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h117207 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step117218 (p2528 p3266 p3707 p4690 p5866 : Prop)
    (h116494 : (¬ p4690) ∨ p2528 ∨ p3266 ∨ (¬ p3707))
    (h117211 : p4690 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p3707) ∨ p3266 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4690) := (Or.elim h116494 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h117211 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117224 (p2528 p3073 p4687 p5866 : Prop)
    (h95396 : p3073 ∨ (¬ p4687) ∨ (¬ p2528))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p2528) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4687) := (Or.elim h95396 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h117208 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117230 (p2608 p2850 p3449 p3641 p4687 p5866 : Prop)
    (h87909 : (¬ p4687) ∨ (¬ p2850) ∨ p2608 ∨ p3641 ∨ (¬ p3449))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p2850) ∨ p3641 ∨ (¬ p3449) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h87909 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117231 (p2493 p3379 p3449 p4598 p4687 p5866 : Prop)
    (h95393 : p3379 ∨ (¬ p4687) ∨ p2493 ∨ (¬ p3449) ∨ (¬ p4598))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p4598) ∨ (¬ p3449) ∨ p2493 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h95393 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117232 (p2608 p3422 p3449 p3641 p4687 p5866 : Prop)
    (h95394 : (¬ p4687) ∨ p3641 ∨ (¬ p3449) ∨ p2608 ∨ (¬ p3422))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p3422) ∨ p3641 ∨ (¬ p3449) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h95394 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117237 (p3083 p3379 p3449 p4687 p4814 p5866 : Prop)
    (h105440 : p4814)
    (h95410 : (¬ p4687) ∨ (¬ p3449) ∨ p3379 ∨ (¬ p4814) ∨ p3083)
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p3449) ∨ p3379 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    let u5 : (¬ p4687) := (Or.elim h95410 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117239 (p2406 p3379 p3449 p4610 p4687 p5866 : Prop)
    (h95414 : (¬ p4687) ∨ (¬ p3449) ∨ p3379 ∨ p2406 ∨ (¬ p4610))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p3449) ∨ p2406 ∨ (¬ p4610) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h95414 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117240 (p2241 p3449 p4149 p4687 p5568 p5866 : Prop)
    (h95420 : (¬ p4149) ∨ (¬ p5568) ∨ p2241 ∨ (¬ p3449) ∨ (¬ p4687))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p5568) ∨ (¬ p4149) ∨ (¬ p3449) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h95420 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117241 (p2651 p3166 p3189 p3641 p4687 p5866 : Prop)
    (h112149 : p3189 ∨ (¬ p4687) ∨ p3641 ∨ p2651 ∨ (¬ p3166))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ p3641 ∨ (¬ p3166) ∨ p3189 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4687) := (Or.elim h112149 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step117246 (p2440 p3379 p3449 p4116 p4610 p4687 p5866 : Prop)
    (h95408 : (¬ p4116) ∨ p3379 ∨ (¬ p2440) ∨ (¬ p3449) ∨ (¬ p4687) ∨ (¬ p4610))
    (h117208 : p4687 ∨ (¬ p5866))
    : (¬ p5866) ∨ (¬ p4116) ∨ (¬ p4610) ∨ (¬ p3449) ∨ p3379 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4687) := (Or.elim h95408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h117208 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

end ElevenRUP
