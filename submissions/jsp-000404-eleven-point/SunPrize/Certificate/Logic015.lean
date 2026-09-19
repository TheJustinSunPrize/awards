import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step54050 (p2027 p3063 p3549 p3550 p4107 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h27716 : p2027 ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666))
    : (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27716 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54055 (p1977 p2027 p2499 p2997 p3097 p3125 p3402 p4137 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h27722 : (¬ p1977) ∨ p2027 ∨ (¬ p2499) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3402) ∨ (¬ p4137))
    : (¬ p2499) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3402) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h27722 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54056 (p2027 p2230 p3055 p3238 p3362 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h27724 : p2027 ∨ (¬ p2230) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3362) ∨ (¬ p5214))
    : (¬ p2230) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3362) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27724 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54060 (p2027 p2254 p2608 p2707 p2717 p2952 p3952 p3989 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27728 : p2027 ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4503))
    : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27728 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54061 (p2027 p2104 p2241 p2264 p2363 p3027 p4340 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h27729 : p2027 ∨ (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27729 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54066 (p2027 p2299 p2589 p3363 p3471 p3527 p3585 p4235 p4424 p4559 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h27734 : p2027 ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3585) ∨ (¬ p4235) ∨ (¬ p4424) ∨ (¬ p4559) ∨ (¬ p4737))
    : (¬ p2299) ∨ (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3585) ∨ (¬ p4235) ∨ (¬ p4424) ∨ (¬ p4559) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27734 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54070 (p2011 p2027 p2210 p2699 p2891 p3105 p4244 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h27739 : (¬ p2011) ∨ p2027 ∨ (¬ p2210) ∨ p2699 ∨ (¬ p2891) ∨ (¬ p3105) ∨ (¬ p4244))
    : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3105) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2011 := h2171;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h27739 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54076 (p2027 p2187 p2459 p3986 p4037 p4133 p4171 : Prop)
    (h40810 : (¬ p2027))
    (h27748 : p2027 ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3986) ∨ (¬ p4037) ∨ (¬ p4133) ∨ (¬ p4171))
    : (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3986) ∨ (¬ p4037) ∨ (¬ p4133) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27748 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54077 (p2027 p2518 p3379 p3425 p3659 p4149 p4348 p4736 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h27749 : p2027 ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4149) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p5122))
    : (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4149) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27749 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54078 (p2027 p3644 p3868 p4133 p4441 p5562 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h27750 : p2027 ∨ (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p5562) ∨ (¬ p5568))
    : (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p5562) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3644 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5562 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27750 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54080 (p2027 p3027 p3552 p4037 p4154 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h27752 : p2027 ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4620))
    : (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3027 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27752 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54081 (p2027 p2246 p2553 p2651 p2744 p2881 p3016 p3366 p3425 p3659 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h27753 : p2027 ∨ (¬ p2246) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4559))
    : (¬ p2246) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27753 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54087 (p1977 p2027 p2462 p2651 p3414 p3947 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h27760 : (¬ p1977) ∨ p2027 ∨ p2462 ∨ (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h27760 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54088 (p1977 p2027 p2579 p2662 p2766 p3956 p4111 p4347 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27761 : (¬ p1977) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2662) ∨ p2766 ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4347))
    : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h27761 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54094 (p1984 p2027 p2202 p2247 p2440 p2518 p2528 p3324 p4116 p4154 p4348 p4503 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27767 : (¬ p1984) ∨ p2027 ∨ p2202 ∨ (¬ p2247) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2247) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1984 := h2144;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2202) := h40867;
    (Or.elim h27767 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u11 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step54096 (p2027 p2248 p2331 p3005 p3238 p3452 p3880 p4195 p5063 : Prop)
    (h40810 : (¬ p2027))
    (h27770 : p2027 ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4195) ∨ (¬ p5063))
    : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4195) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27770 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54097 (p2027 p2284 p2992 p2996 p3699 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h27771 : p2027 ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555))
    : (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27771 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54099 (p2027 p2363 p2774 p2819 p2928 p3452 p4278 p4669 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h27774 : p2027 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733))
    : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27774 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54102 (p1984 p2027 p2363 p2641 p2668 p2688 p3238 p3452 p3880 p4348 p4905 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h27778 : (¬ p1984) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ p2688 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1984 := h2144;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2688) := h40880;
    (Or.elim h27778 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u10 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step54107 (p2027 p2717 p2737 p3551 p3820 p4734 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h27783 : p2027 ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734) ∨ (¬ p4781))
    : (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27783 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54110 (p2027 p2449 p2881 p3551 p4107 p4155 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h27786 : p2027 ∨ (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4155) ∨ (¬ p4559))
    : (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4155) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27786 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54111 (p1984 p2027 p2191 p2972 p3369 p3982 p4032 p5568 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h27787 : (¬ p1984) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2972) ∨ (¬ p3369) ∨ p3982 ∨ (¬ p4032) ∨ (¬ p5568))
    : (¬ p2191) ∨ (¬ p2972) ∨ (¬ p3369) ∨ (¬ p4032) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3982) := h40909;
    (Or.elim h27787 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54113 (p1976 p2027 p2737 p3008 p3365 p3574 p3585 p4343 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h27789 : (¬ p1976) ∨ p2027 ∨ (¬ p2737) ∨ p3008 ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4343))
    : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h27789 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54115 (p2027 p2088 p2249 p2499 p2657 p3027 p3171 p3487 p3956 p4044 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27791 : p2027 ∨ (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3487) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3487) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27791 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54117 (p2027 p2220 p2499 p3146 p3452 p3956 p4348 p4503 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h27793 : p2027 ∨ (¬ p2220) ∨ (¬ p2499) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4521))
    : (¬ p2220) ∨ (¬ p2499) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27793 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54120 (p2027 p2248 p2499 p2807 p3256 p3452 p3956 p4044 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27796 : p2027 ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27796 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54127 (p1994 p2027 p2114 p2138 p2630 p2696 p2839 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27803 : (¬ p1994) ∨ p2027 ∨ p2114 ∨ (¬ p2138) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2839))
    : (¬ p2138) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h27803 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54129 (p2027 p3276 p3358 p4322 p4355 p4385 p4882 : Prop)
    (h40810 : (¬ p2027))
    (h27805 : p2027 ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4322) ∨ (¬ p4355) ∨ (¬ p4385) ∨ (¬ p4882))
    : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4322) ∨ (¬ p4355) ∨ (¬ p4385) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27805 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54130 (p2027 p2589 p2608 p2707 p2717 p3989 p4110 p4503 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27806 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27806 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54135 (p2027 p2241 p2264 p2589 p3027 p3989 p4110 p4503 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27814 : p2027 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27814 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54141 (p2027 p2528 p4009 p4118 p4434 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h27822 : p2027 ∨ (¬ p2528) ∨ (¬ p4009) ∨ (¬ p4118) ∨ (¬ p4434) ∨ (¬ p5568))
    : (¬ p2528) ∨ (¬ p4009) ∨ (¬ p4118) ∨ (¬ p4434) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27822 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54149 (p2027 p2132 p2363 p2476 p2534 p2750 p2753 p2870 p2881 p3347 p3402 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27832 : p2027 ∨ (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3347) ∨ (¬ p3402) ∨ (¬ p4503))
    : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3347) ∨ (¬ p3402) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27832 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54151 (p1997 p2027 p2476 p2542 p3389 p3498 p3742 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h27836 : (¬ p1997) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2542) ∨ (¬ p3389) ∨ p3498 ∨ (¬ p3742))
    : (¬ p2476) ∨ (¬ p2542) ∨ (¬ p3389) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h27836 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54156 (p2027 p2630 p2655 p2922 p3540 p4116 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h27844 : p2027 ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4116) ∨ (¬ p4787))
    : (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4116) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27844 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54157 (p2027 p2630 p3083 p3572 p3879 p4156 p4336 p4610 : Prop)
    (h40810 : (¬ p2027))
    (h27845 : p2027 ∨ (¬ p2630) ∨ (¬ p3083) ∨ (¬ p3572) ∨ (¬ p3879) ∨ (¬ p4156) ∨ (¬ p4336) ∨ (¬ p4610))
    : (¬ p2630) ∨ (¬ p3083) ∨ (¬ p3572) ∨ (¬ p3879) ∨ (¬ p4156) ∨ (¬ p4336) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27845 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54162 (p2027 p2166 p2210 p2459 p2534 p3347 p3540 p3954 p4186 p4902 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h27850 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p5216))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27850 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54164 (p2027 p2295 p2313 p2946 p3983 p4563 : Prop)
    (h40810 : (¬ p2027))
    (h27852 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3983) ∨ (¬ p4563))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3983) ∨ (¬ p4563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27852 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54173 (p1977 p2027 p2177 p2241 p2997 p3548 p4366 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h27861 : (¬ p1977) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2241) ∨ p2997 ∨ (¬ p3548) ∨ (¬ p4366))
    : (¬ p2177) ∨ (¬ p2241) ∨ (¬ p3548) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h27861 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54175 (p2027 p2264 p2363 p2696 p2742 p3027 p3688 p4078 p4340 p4503 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h27864 : p2027 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737))
    : (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27864 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54182 (p2027 p2598 p2911 p3201 p3555 p3989 p4173 p4503 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h27871 : p2027 ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4503) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27871 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54184 (p2027 p2470 p2528 p3555 p3989 p4173 p4348 p4503 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h27875 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27875 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54188 (p1982 p2027 p2114 p2657 p2727 p2749 p3166 p3256 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27879 : (¬ p1982) ∨ p2027 ∨ p2114 ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h27879 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54190 (p2027 p2156 p2850 p3952 p4109 p4700 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h27881 : p2027 ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4753))
    : (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27881 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54192 (p2027 p2396 p2891 p4363 p4382 p4556 : Prop)
    (h40810 : (¬ p2027))
    (h27884 : p2027 ∨ (¬ p2396) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4556))
    : (¬ p2396) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27884 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54195 (p1982 p2027 p2633 p3246 p3570 p3767 p4444 p5295 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27887 : (¬ p1982) ∨ p2027 ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3767) ∨ (¬ p4444) ∨ (¬ p5295))
    : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3767) ∨ (¬ p4444) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h27887 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54197 (p2007 p2027 p2241 p2534 p2699 p3189 p3256 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h27892 : (¬ p2007) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2534) ∨ p2699 ∨ (¬ p3189) ∨ (¬ p3256))
    : (¬ p2241) ∨ (¬ p2534) ∨ (¬ p3189) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2007 := h2167;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h27892 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54198 (p2027 p2341 p2363 p3821 p4445 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27894 : p2027 ∨ (¬ p2341) ∨ (¬ p2363) ∨ (¬ p3821) ∨ (¬ p4445) ∨ (¬ p4503))
    : (¬ p2341) ∨ (¬ p2363) ∨ (¬ p3821) ∨ (¬ p4445) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27894 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54200 (p2027 p2264 p2363 p2598 p3201 p3688 p3740 p4078 p4340 p4503 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h27898 : p2027 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3688) ∨ (¬ p3740) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737))
    : (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3688) ∨ (¬ p3740) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27898 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54202 (p2027 p2156 p2901 p3556 p4110 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h27900 : p2027 ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27900 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54203 (p2027 p2406 p2509 p3156 p3693 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h27901 : p2027 ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p4705))
    : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54204 (p2027 p2441 p2901 p3246 p4278 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h27902 : p2027 ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4705))
    : (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54207 (p2027 p2427 p3661 p3691 p3767 p4349 p4702 p5284 p5300 : Prop)
    (h40810 : (¬ p2027))
    (h27905 : p2027 ∨ (¬ p2427) ∨ (¬ p3661) ∨ (¬ p3691) ∨ (¬ p3767) ∨ (¬ p4349) ∨ (¬ p4702) ∨ (¬ p5284) ∨ (¬ p5300))
    : (¬ p2427) ∨ (¬ p3661) ∨ (¬ p3691) ∨ (¬ p3767) ∨ (¬ p4349) ∨ (¬ p4702) ∨ (¬ p5284) ∨ (¬ p5300) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5300 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27905 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54208 (p2027 p2241 p2264 p2363 p3027 p3646 p3692 p3988 p4503 p4524 : Prop)
    (h40810 : (¬ p2027))
    (h27906 : p2027 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4503) ∨ (¬ p4524))
    : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4503) ∨ (¬ p4524) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27906 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54209 (p2027 p2819 p3985 p3989 p4244 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h27907 : p2027 ∨ (¬ p2819) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p4244) ∨ (¬ p4555))
    : (¬ p2819) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p4244) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27907 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54212 (p2027 p2295 p2579 p2588 p3019 p3347 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h27910 : p2027 ∨ (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p3347) ∨ (¬ p4811))
    : (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p3347) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27910 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54213 (p1994 p2027 p2651 p2764 p2952 p3879 p4322 p4948 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h27911 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ p2764 ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4322) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h27911 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54217 (p2027 p2255 p2579 p2662 p3166 p3256 p3956 p4111 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27915 : p2027 ∨ (¬ p2255) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2255) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4111) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27915 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54220 (p1994 p2027 p2247 p2406 p2440 p2688 p3379 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h27918 : (¬ p1994) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2440) ∨ p2688 ∨ (¬ p3379))
    : (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h27918 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54221 (p2027 p2579 p2662 p2810 p3136 p4241 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h27919 : p2027 ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4715))
    : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54222 (p1998 p2027 p2579 p2842 p2911 p3389 p3422 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h27920 : (¬ p1998) ∨ p2027 ∨ (¬ p2579) ∨ p2842 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3422))
    : (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h27920 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54223 (p2027 p2579 p3389 p3422 p3742 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h27921 : p2027 ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3742) ∨ (¬ p4753))
    : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3742) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27921 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54231 (p1992 p2027 p2608 p2938 p3238 p3452 p4235 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h27930 : (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ p2938 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4235))
    : (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h27930 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54233 (p1998 p2027 p2914 p3073 p3083 p3742 p4348 p4370 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h27932 : (¬ p1998) ∨ p2027 ∨ p2914 ∨ (¬ p3073) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p4348) ∨ (¬ p4370))
    : (¬ p3073) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p4348) ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h27932 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54235 (p2027 p2911 p2922 p3324 p3365 p3379 p4195 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h27934 : p2027 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p4195) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p4195) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27934 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54237 (p2027 p2743 p3367 p3683 p3877 p5008 : Prop)
    (h40810 : (¬ p2027))
    (h27936 : p2027 ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p3877) ∨ (¬ p5008))
    : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p3877) ∨ (¬ p5008) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27936 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54238 (p2027 p2156 p2901 p2911 p3548 p3952 p4366 p4521 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h27937 : p2027 ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4521) ∨ (¬ p4647))
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4521) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27937 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54241 (p1976 p2027 p2388 p2743 p3055 p3367 p4315 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h27940 : (¬ p1976) ∨ p2027 ∨ p2388 ∨ (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4315))
    : (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h27940 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54242 (p1998 p2027 p2622 p2707 p2743 p2881 p3434 p3690 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27941 : (¬ p1998) ∨ p2027 ∨ p2622 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p3690))
    : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h27941 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54243 (p2027 p2254 p2657 p3073 p3449 p3574 p3956 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27942 : p2027 ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27942 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54245 (p2001 p2027 p2148 p2156 p2187 p2363 p3692 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h27944 : (¬ p2001) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3692))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h27944 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54246 (p2027 p2241 p2579 p2992 p3115 p3956 p4347 p4450 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27946 : p2027 ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27946 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54247 (p2027 p2166 p2210 p2254 p3414 p3947 p3969 p4381 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h27947 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3969) ∨ (¬ p4381) ∨ (¬ p5119))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3969) ∨ (¬ p4381) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27947 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54250 (p2027 p2210 p2363 p2476 p2534 p2881 p2891 p4503 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27950 : p2027 ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4503) ∨ (¬ p5193))
    : (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4503) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27950 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54251 (p2000 p2027 p2177 p2462 p3540 p3644 p4107 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h27951 : (¬ p2000) ∨ p2027 ∨ (¬ p2177) ∨ p2462 ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h27951 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54252 (p1992 p2027 p2202 p2440 p2668 p3019 p3688 p4358 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27952 : (¬ p1992) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3688) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h27952 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54253 (p1976 p2027 p2462 p2476 p3641 p3876 p3905 p4278 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h27953 : (¬ p1976) ∨ p2027 ∨ p2462 ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4278))
    : (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h27953 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54256 (p2027 p2210 p2254 p2363 p2881 p2891 p2963 p4118 p4196 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27956 : p2027 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503))
    : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27956 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54257 (p2027 p3323 p3324 p4345 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27957 : p2027 ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27957 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54258 (p2010 p2027 p2476 p2534 p3146 p3389 p3578 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h27958 : (¬ p2010) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3389) ∨ p3578)
    : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3578) := h40900;
    (Or.elim h27958 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step54259 (p1990 p2027 p2295 p2829 p3097 p3474 p3583 p4328 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h27959 : (¬ p1990) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2829) ∨ (¬ p3097) ∨ p3474 ∨ (¬ p3583) ∨ (¬ p4328))
    : (¬ p2295) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3474) := h40898;
    (Or.elim h27959 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54261 (p1991 p2027 p2274 p2588 p2657 p2765 p3574 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h27961 : (¬ p1991) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2657) ∨ p2765 ∨ (¬ p3574))
    : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h27961 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54264 (p1993 p2027 p2287 p2651 p2810 p2963 p3005 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h27967 : (¬ p1993) ∨ p2027 ∨ p2287 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3005))
    : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1993 := h2153;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h27967 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54265 (p2027 p2156 p2177 p2274 p2528 p3452 p3453 p4261 p4438 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h27968 : p2027 ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4521))
    : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27968 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54274 (p2027 p2427 p4129 p4386 p4391 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h27981 : p2027 ∨ (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) ∨ (¬ p4702))
    : (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27981 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54277 (p2027 p2098 p2247 p3324 p3609 p4154 p4348 p4503 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h27985 : p2027 ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p3609) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2098) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p3609) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27985 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54280 (p2027 p2138 p2406 p2598 p3698 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h27989 : p2027 ∨ (¬ p2138) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p3698) ∨ (¬ p5217))
    : (¬ p2138) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p3698) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27989 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54283 (p2027 p2363 p2780 p2911 p3367 p3389 p3759 p4078 p4340 p4503 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h27992 : p2027 ∨ (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4734))
    : (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27992 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54293 (p2027 p2098 p3555 p3609 p3989 p4173 p4348 p4503 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28004 : p2027 ∨ (¬ p2098) ∨ (¬ p3555) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2098) ∨ (¬ p3555) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28004 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54298 (p1998 p2027 p2177 p2449 p2765 p2995 p3952 p4278 p4710 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h28011 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2449) ∨ p2765 ∨ (¬ p2995) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4710))
    : (¬ p2177) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1998 := h2158;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2765) := h40883;
    (Or.elim h28011 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54300 (p1975 p2027 p2299 p2622 p2630 p2656 p2911 p3389 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28013 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2911) ∨ (¬ p3389))
    : (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2911) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h28013 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54302 (p2027 p2230 p2247 p2427 p2608 p2881 p3031 p3519 p3817 p4376 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h28015 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3031) ∨ (¬ p3519) ∨ (¬ p3817) ∨ (¬ p4376) ∨ (¬ p4666))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3031) ∨ (¬ p3519) ∨ (¬ p3817) ∨ (¬ p4376) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28015 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54304 (p2027 p2230 p2427 p2608 p2881 p3519 p3591 p3923 p4376 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28017 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p4503))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28017 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54307 (p1998 p2027 p2396 p2873 p2881 p3309 p3690 p4338 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h28020 : (¬ p1998) ∨ p2027 ∨ (¬ p2396) ∨ p2873 ∨ (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4338))
    : (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2873) := h40886;
    (Or.elim h28020 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54312 (p1998 p2027 p2417 p2437 p2545 p3527 p3817 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28025 : (¬ p1998) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2437) ∨ p2545 ∨ (¬ p3527) ∨ (¬ p3817))
    : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3527) ∨ (¬ p3817) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h28025 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54313 (p1976 p2027 p2437 p2545 p2737 p3365 p3585 p3876 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28026 : (¬ p1976) ∨ p2027 ∨ (¬ p2437) ∨ p2545 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p3876))
    : (¬ p2437) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h28026 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54315 (p2027 p2132 p2245 p2363 p2870 p2881 p2963 p4118 p4196 p4503 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28030 : p2027 ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28030 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54316 (p1998 p2027 p2363 p2388 p3189 p3662 p4348 p4417 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h28031 : (¬ p1998) ∨ p2027 ∨ (¬ p2363) ∨ p2388 ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4417))
    : (¬ p2363) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h28031 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54317 (p2027 p2247 p2470 p2528 p3324 p4154 p4348 p4503 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h28033 : p2027 ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190))
    : (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28033 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54321 (p2027 p2668 p2696 p2797 p3097 p3555 p4173 p4405 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28039 : p2027 ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4733))
    : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28039 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54322 (p2027 p2331 p2589 p3506 p3690 p4117 p4191 p4235 p4421 p4621 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h28040 : p2027 ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4235) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4729))
    : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4235) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28040 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54328 (p2027 p2470 p2528 p3324 p3365 p4079 p4195 p4348 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28050 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28050 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54329 (p2027 p2284 p2590 p3654 p3743 p4137 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28051 : p2027 ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4137) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4137) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28051 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54331 (p2027 p2341 p2441 p2901 p3644 p3691 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28053 : p2027 ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705))
    : (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28053 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54333 (p2027 p2850 p3156 p3693 p3874 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28055 : p2027 ∨ (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p4705))
    : (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28055 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54336 (p2027 p2441 p2881 p2901 p3644 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28058 : p2027 ∨ (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p4705))
    : (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28058 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54337 (p2027 p2254 p2363 p2911 p2922 p3172 p3379 p4118 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28059 : p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p4118) ∨ (¬ p4503))
    : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p4118) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28059 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54341 (p2027 p2255 p2363 p2651 p2911 p2922 p3177 p3857 p4116 p4360 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28064 : p2027 ∨ (¬ p2255) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4116) ∨ (¬ p4360) ∨ (¬ p4503))
    : (¬ p2255) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4116) ∨ (¬ p4360) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28064 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54342 (p2027 p3051 p3156 p3688 p3954 p4042 p4320 p4358 p4503 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h28065 : p2027 ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521))
    : (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28065 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54343 (p2027 p2253 p2750 p3166 p3954 p4360 : Prop)
    (h40810 : (¬ p2027))
    (h28066 : p2027 ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p3166) ∨ (¬ p3954) ∨ (¬ p4360))
    : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p3166) ∨ (¬ p3954) ∨ (¬ p4360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28066 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54345 (p1987 p2027 p2598 p2699 p2749 p2992 p3585 p3589 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28068 : (¬ p1987) ∨ p2027 ∨ (¬ p2598) ∨ p2699 ∨ (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4315))
    : (¬ p2598) ∨ (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1987 := h2147;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h28068 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54346 (p1992 p2027 p2143 p2169 p2274 p2313 p3583 p3989 p4198 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28069 : (¬ p1992) ∨ p2027 ∨ (¬ p2143) ∨ p2169 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4198))
    : (¬ p2143) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2169) := h40866;
    (Or.elim h28069 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54348 (p2027 p2138 p3073 p3449 p3758 p3989 p4348 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28071 : p2027 ∨ (¬ p2138) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2138) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28071 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54349 (p2027 p2138 p2911 p2922 p3379 p3758 p3989 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28072 : p2027 ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28072 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54351 (p2027 p2363 p2911 p2922 p3379 p3692 p4120 p4503 p4524 : Prop)
    (h40810 : (¬ p2027))
    (h28074 : p2027 ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4503) ∨ (¬ p4524))
    : (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4503) ∨ (¬ p4524) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28074 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54352 (p2027 p2313 p2787 p2946 p3644 p3755 p4117 p4315 p4348 p4710 p5109 : Prop)
    (h40810 : (¬ p2027))
    (h28075 : p2027 ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4348) ∨ (¬ p4710) ∨ (¬ p5109))
    : (¬ p2313) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4348) ∨ (¬ p4710) ∨ (¬ p5109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28075 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54353 (p2027 p2246 p2498 p2749 p2946 p3005 p3379 p3591 p3956 p4315 p4771 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h28076 : p2027 ∨ (¬ p2246) ∨ (¬ p2498) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4315) ∨ (¬ p4771) ∨ (¬ p5216))
    : (¬ p2246) ∨ (¬ p2498) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4315) ∨ (¬ p4771) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28076 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54355 (p2027 p2685 p4066 p4235 p4283 p4315 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28080 : p2027 ∨ (¬ p2685) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4315) ∨ (¬ p4705))
    : (¬ p2685) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4315) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28080 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54357 (p2006 p2027 p2166 p2873 p3051 p4120 p4244 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h28082 : (¬ p2006) ∨ p2027 ∨ (¬ p2166) ∨ p2873 ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4244))
    : (¬ p2166) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2006 := h2166;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2873) := h40886;
    (Or.elim h28082 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54361 (p2027 p2230 p2247 p2427 p2881 p3324 p4154 p4503 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h28086 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28086 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54363 (p2027 p3319 p3923 p4345 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28088 : p2027 ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28088 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54364 (p2027 p2241 p2598 p2750 p2753 p2911 p3201 p3591 p3923 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28089 : p2027 ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503))
    : (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28089 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54366 (p2027 p2797 p2810 p2963 p3286 p5177 : Prop)
    (h40810 : (¬ p2027))
    (h28091 : p2027 ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p5177))
    : (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p5177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28091 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54367 (p2027 p2470 p2528 p2797 p2963 p3877 p4041 p4236 p4348 p4419 : Prop)
    (h40810 : (¬ p2027))
    (h28092 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4419))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28092 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54371 (p2027 p2284 p2386 p2406 p2499 p3743 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28098 : p2027 ∨ (¬ p2284) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3743) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28098 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54373 (p1991 p2027 p2462 p2881 p3414 p3553 p3690 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h28100 : (¬ p1991) ∨ p2027 ∨ p2462 ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3690))
    : (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h28100 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54374 (p2027 p2307 p2440 p2657 p2786 p2819 p3822 p3880 p4134 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h28101 : p2027 ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4789))
    : (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28101 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54375 (p2027 p2499 p2573 p2737 p3759 p4257 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h28104 : p2027 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28104 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54376 (p2027 p3156 p3949 p3969 p4208 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h28105 : p2027 ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p3969) ∨ (¬ p4208) ∨ (¬ p5122))
    : (¬ p3156) ∨ (¬ p3949) ∨ (¬ p3969) ∨ (¬ p4208) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28105 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54378 (p1985 p2027 p2608 p2699 p2707 p3434 p3690 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28107 : (¬ p1985) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3690))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h28107 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54382 (p1975 p2027 p2553 p2584 p2622 p2630 p2656 p3654 p4137 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28112 : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2584) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p2553) ∨ (¬ p2584) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3654) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h28112 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54384 (p2027 p2284 p2319 p2341 p2441 p3644 p3743 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28114 : p2027 ∨ (¬ p2284) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p3644) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p3644) ∨ (¬ p3743) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28114 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54385 (p2027 p3166 p3414 p3644 p4653 p5074 p5307 : Prop)
    (h40810 : (¬ p2027))
    (h28115 : p2027 ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p5074) ∨ (¬ p5307))
    : (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p5074) ∨ (¬ p5307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28115 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54386 (p2027 p2299 p2313 p2406 p2982 p3379 p4348 p4450 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h28116 : p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28116 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54389 (p2027 p2132 p2860 p4232 p5026 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h28119 : p2027 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4232) ∨ (¬ p5026) ∨ (¬ p5043))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4232) ∨ (¬ p5026) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28119 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54390 (p1982 p2027 p2459 p2656 p2688 p2727 p2911 p3389 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h28120 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389))
    : (¬ p2459) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h28120 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54391 (p1982 p2027 p2765 p2972 p3412 p3680 p3952 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h28121 : (¬ p1982) ∨ p2027 ∨ p2765 ∨ (¬ p2972) ∨ (¬ p3412) ∨ (¬ p3680) ∨ (¬ p3952) ∨ (¬ p4444))
    : (¬ p2972) ∨ (¬ p3412) ∨ (¬ p3680) ∨ (¬ p3952) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h28121 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54392 (p2027 p2210 p2881 p2891 p3055 p3876 p4278 p4666 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28122 : p2027 ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4736))
    : (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28122 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54393 (p1987 p2027 p2737 p3551 p3588 p3959 p3982 p5558 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h28125 : (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ p3982 ∨ (¬ p5558))
    : (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3982) := h40909;
    (Or.elim h28125 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54397 (p1992 p2027 p2608 p2911 p2914 p3548 p4366 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h28129 : (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3548) ∨ (¬ p4366))
    : (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h28129 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54398 (p2027 p2210 p2247 p2744 p2891 p2911 p3347 p3551 p3741 p4110 p4257 p4558 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h28130 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3347) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4257) ∨ (¬ p4558) ∨ (¬ p5197))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3347) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4257) ∨ (¬ p4558) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h28130 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step54399 (p2027 p2138 p2331 p2363 p2668 p3690 p4244 p4669 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h28131 : p2027 ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786))
    : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28131 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54400 (p2027 p2138 p2807 p3506 p3692 p3694 p3950 p4381 p4661 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h28132 : p2027 ∨ (¬ p2138) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4786))
    : (¬ p2138) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28132 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54402 (p2027 p2819 p3573 p3979 p4286 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h28135 : p2027 ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p5225))
    : (¬ p2819) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28135 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54403 (p2027 p2246 p2284 p2608 p2744 p2946 p3125 p3860 p4261 p4330 : Prop)
    (h40810 : (¬ p2027))
    (h28140 : p2027 ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330))
    : (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28140 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54412 (p2027 p2230 p2982 p3365 p3572 p3680 p4391 p4419 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h28152 : p2027 ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4831))
    : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28152 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54414 (p2027 p2341 p2657 p3246 p3366 p3370 p3570 p3584 p3683 p4137 p4236 p4377 p4625 p4988 : Prop)
    (h40810 : (¬ p2027))
    (h28154 : p2027 ∨ (¬ p2341) ∨ (¬ p2657) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4625) ∨ (¬ p4988))
    : (¬ p2341) ∨ (¬ p2657) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4625) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h28154 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step54417 (p1976 p2027 p2169 p2579 p3483 p3905 p4137 p4358 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28158 : (¬ p1976) ∨ p2027 ∨ p2169 ∨ (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p4137) ∨ (¬ p4358))
    : (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p4137) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h28158 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54418 (p2027 p3434 p3587 p3690 p3952 p4316 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28160 : p2027 ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p4558))
    : (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28160 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54419 (p2027 p2191 p2220 p2891 p3646 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28161 : p2027 ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2891) ∨ (¬ p3646) ∨ (¬ p4558))
    : (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2891) ∨ (¬ p3646) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28161 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54420 (p2027 p2459 p2717 p3857 p3961 p5258 : Prop)
    (h40810 : (¬ p2027))
    (h28162 : p2027 ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p5258))
    : (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p5258) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5258 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28162 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54424 (p2027 p2383 p2586 p3016 p4256 p4432 : Prop)
    (h40810 : (¬ p2027))
    (h28167 : p2027 ∨ (¬ p2383) ∨ (¬ p2586) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4432))
    : (¬ p2383) ∨ (¬ p2586) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28167 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54428 (p1994 p2027 p2299 p2588 p3574 p3982 p5558 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h28173 : (¬ p1994) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3574) ∨ p3982 ∨ (¬ p5558))
    : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3982) := h40909;
    (Or.elim h28173 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54429 (p2027 p2253 p2299 p2780 p2946 p3256 p3692 p3822 p4237 p4736 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h28174 : p2027 ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4237) ∨ (¬ p4736) ∨ (¬ p4902))
    : (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4237) ∨ (¬ p4736) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28174 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54430 (p2027 p3051 p3125 p3946 p4198 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28175 : p2027 ∨ (¬ p3051) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4558))
    : (¬ p3051) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28175 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54439 (p2027 p2104 p2352 p2459 p2651 p3016 p4133 p4340 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h28186 : p2027 ∨ (¬ p2104) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4786))
    : (¬ p2104) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28186 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54442 (p2027 p2476 p2518 p2608 p4108 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h28189 : p2027 ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376))
    : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54444 (p1976 p2027 p2881 p2938 p3055 p3644 p3876 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h28192 : (¬ p1976) ∨ p2027 ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p2881) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h28192 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54448 (p1982 p2363 p2668 p3008 p4973 : Prop)
    (h2142 : p1982)
    (h40891 : (¬ p3008))
    (h28196 : (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2668) ∨ p3008 ∨ p4973)
    : (¬ p2363) ∨ (¬ p2668) ∨ p4973 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4973) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1982 := h2142;
    let u4 : (¬ p3008) := h40891;
    (Or.elim h28196 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step54449 (p1982 p2027 p2459 p2717 p2842 p3055 p3471 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h28198 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2717) ∨ p2842 ∨ (¬ p3055) ∨ (¬ p3471))
    : (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3055) ∨ (¬ p3471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h28198 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54451 (p1986 p2027 p2138 p2598 p2633 p3486 p3570 p4243 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28202 : (¬ p1986) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ p2633 ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4243))
    : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h28202 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54452 (p2027 p2191 p2619 p3051 p3370 p3758 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28203 : p2027 ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3758) ∨ (¬ p4558))
    : (¬ p2191) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3758) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28203 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54454 (p2027 p2383 p3323 p3324 p3583 p3954 p4368 p4385 p5017 : Prop)
    (h40810 : (¬ p2027))
    (h28205 : p2027 ∨ (¬ p2383) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4368) ∨ (¬ p4385) ∨ (¬ p5017))
    : (¬ p2383) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4368) ∨ (¬ p4385) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28205 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54456 (p2027 p2588 p2870 p3758 p3958 p4140 : Prop)
    (h40810 : (¬ p2027))
    (h28209 : p2027 ∨ (¬ p2588) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p3958) ∨ (¬ p4140))
    : (¬ p2588) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p3958) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28209 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54457 (p1982 p2027 p2132 p2619 p2622 p2743 p2753 p3146 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28211 : (¬ p1982) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2619) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3146))
    : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h28211 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54460 (p2027 p2104 p2248 p2363 p2881 p2901 p2946 p3873 p4340 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28216 : p2027 ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4503))
    : (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28216 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54461 (p1998 p2027 p2619 p2765 p3146 p3758 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h28217 : (¬ p1998) ∨ p2027 ∨ (¬ p2619) ∨ p2765 ∨ (¬ p3146) ∨ (¬ p3758) ∨ (¬ p4348))
    : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3758) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h28217 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54462 (p2027 p2220 p3146 p3688 p3954 p4348 p4358 p4503 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h28218 : p2027 ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521))
    : (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28218 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54463 (p1994 p2027 p2323 p2440 p2807 p2850 p3475 p3572 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h28219 : (¬ p1994) ∨ p2027 ∨ p2323 ∨ (¬ p2440) ∨ (¬ p2807) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572))
    : (¬ p2440) ∨ (¬ p2807) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h28219 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54466 (p1998 p2027 p2114 p2717 p2737 p3365 p3471 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28223 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471))
    : (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h28223 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54468 (p1994 p2027 p2323 p2663 p3389 p3422 p3574 p3876 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h28225 : (¬ p1994) ∨ p2027 ∨ p2323 ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876))
    : (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2663 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h28225 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54470 (p2027 p2264 p2363 p2534 p2579 p2685 p2696 p2753 p3347 p3573 p4503 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h28227 : p2027 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3573) ∨ (¬ p4503) ∨ (¬ p5216))
    : (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3573) ∨ (¬ p4503) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28227 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54471 (p1994 p2027 p2440 p2997 p3097 p3125 p3946 p4031 p4198 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h28229 : (¬ p1994) ∨ p2027 ∨ (¬ p2440) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198))
    : (¬ p2440) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h28229 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54472 (p2027 p2299 p2579 p2588 p3347 p3449 p3544 p3631 p3954 p4668 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h28230 : p2027 ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3544) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5216))
    : (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3544) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28230 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54482 (p2027 p2098 p2780 p3989 p4326 p4401 : Prop)
    (h40810 : (¬ p2027))
    (h28243 : p2027 ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4326) ∨ (¬ p4401))
    : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4326) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28243 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54483 (p1996 p2027 p2202 p2417 p2589 p3389 p3947 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28244 : (¬ p1996) ∨ p2027 ∨ p2202 ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3947))
    : (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h28244 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54486 (p2027 p2191 p2528 p3692 p4355 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h28247 : p2027 ∨ (¬ p2191) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4629))
    : (¬ p2191) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28247 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54488 (p2027 p2136 p2247 p2744 p3366 p3399 p3692 p4075 p4120 p4444 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h28249 : p2027 ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p4075) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826))
    : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p4075) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28249 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54490 (p2027 p2241 p2579 p2588 p3506 p3842 p4260 p4831 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h28251 : p2027 ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28251 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54491 (p2027 p2246 p2608 p2744 p2807 p3256 p3591 p3918 p4044 p4348 p4358 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28252 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28252 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54492 (p2027 p2780 p2881 p2901 p2946 p3822 p4107 p4666 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h28253 : p2027 ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4786))
    : (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2780 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28253 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54494 (p2027 p2241 p2641 p2911 p3323 p3551 p4278 p4621 p5193 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h28255 : p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p5193) ∨ (¬ p5197))
    : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p5193) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28255 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54495 (p1998 p2027 p2202 p2563 p2881 p2901 p3952 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28256 : (¬ p1998) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3952))
    : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h28256 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54496 (p1987 p2027 p2169 p2313 p2553 p2577 p2810 p3347 p3487 p3956 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28257 : (¬ p1987) ∨ p2027 ∨ p2169 ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2810) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3956))
    : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2810) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1987 := h2147;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2169) := h40866;
    (Or.elim h28257 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step54497 (p1994 p2027 p2440 p2459 p2633 p3556 p3692 p4031 p4119 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28258 : (¬ p1994) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4031) ∨ (¬ p4119))
    : (¬ p2440) ∨ (¬ p2459) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4031) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h28258 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54512 (p2027 p2138 p2166 p3371 p3694 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h28274 : p2027 ∨ (¬ p2138) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3694) ∨ (¬ p4734))
    : (¬ p2138) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3694) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28274 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54518 (p2027 p2241 p2493 p2579 p2750 p3541 p4108 : Prop)
    (h40810 : (¬ p2027))
    (h28282 : p2027 ∨ (¬ p2241) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108))
    : (¬ p2241) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28282 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54519 (p2027 p2088 p2319 p2563 p3957 p4340 p4359 p4590 p4882 p5016 : Prop)
    (h40810 : (¬ p2027))
    (h28283 : p2027 ∨ (¬ p2088) ∨ (¬ p2319) ∨ (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4590) ∨ (¬ p4882) ∨ (¬ p5016))
    : (¬ p2088) ∨ (¬ p2319) ∨ (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4590) ∨ (¬ p4882) ∨ (¬ p5016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28283 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54532 (p2027 p2104 p2230 p2363 p2427 p2881 p3366 p3519 p4340 p4376 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h28299 : p2027 ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2363) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4503))
    : (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2363) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28299 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54533 (p2027 p3266 p3292 p3366 p3399 p3452 p3631 p3950 p4236 p4376 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h28300 : p2027 ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5284))
    : (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28300 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54534 (p2027 p2241 p2750 p2753 p3324 p3471 p3591 p3609 p4319 p4348 p4503 p4805 : Prop)
    (h40810 : (¬ p2027))
    (h28301 : p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3324) ∨ (¬ p3471) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p4319) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4805))
    : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3324) ∨ (¬ p3471) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p4319) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4805) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28301 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54535 (p1976 p2027 p2545 p2992 p3365 p4111 p4315 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28302 : (¬ p1976) ∨ p2027 ∨ p2545 ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4315))
    : (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h28302 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54536 (p2027 p2192 p2901 p3486 p4110 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28303 : p2027 ∨ (¬ p2192) ∨ (¬ p2901) ∨ (¬ p3486) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2192) ∨ (¬ p2901) ∨ (¬ p3486) ∨ (¬ p4110) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28303 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54538 (p2027 p2341 p2590 p2901 p3581 p3644 p3691 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h28305 : p2027 ∨ (¬ p2341) ∨ (¬ p2590) ∨ (¬ p2901) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705))
    : (¬ p2341) ∨ (¬ p2590) ∨ (¬ p2901) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28305 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54540 (p1982 p2027 p2363 p2470 p2545 p2579 p3016 p4157 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28307 : (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2470) ∨ p2545 ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p4157))
    : (¬ p2363) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p4157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h28307 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54542 (p2027 p2104 p2210 p2363 p2881 p2891 p4340 p4503 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28309 : p2027 ∨ (¬ p2104) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p2104) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28309 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54543 (p2027 p2363 p2598 p2911 p2963 p3201 p4118 p4196 p4503 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h28310 : p2027 ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4789))
    : (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4503) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28310 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54548 (p1987 p2027 p2114 p2241 p2727 p2810 p3954 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28315 : (¬ p1987) ∨ p2027 ∨ p2114 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p3954))
    : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h28315 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54549 (p2027 p2829 p3585 p3876 p4390 p4708 : Prop)
    (h40810 : (¬ p2027))
    (h28316 : p2027 ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p4390) ∨ (¬ p4708))
    : (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p4390) ∨ (¬ p4708) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28316 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54550 (p2027 p2274 p2312 p2341 p3548 p4105 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h28317 : p2027 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p4514))
    : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28317 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54551 (p1987 p2027 p2344 p2383 p2737 p3688 p4358 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h28318 : (¬ p1987) ∨ p2027 ∨ p2344 ∨ (¬ p2383) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2383) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2344) := h40871;
    (Or.elim h28318 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54553 (p1982 p2027 p2518 p2528 p2952 p2997 p3097 p3136 p3379 p3745 p4195 p4236 p4736 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h28320 : (¬ p1982) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4736))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p1982 := h2142;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2997) := h40890;
    (Or.elim h28320 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u12 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step54558 (p1983 p2027 p2114 p2299 p2319 p2341 p2396 p2779 p2829 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28328 : (¬ p1983) ∨ p2027 ∨ p2114 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2779) ∨ (¬ p2829))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2779) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h28328 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54560 (p2027 p2307 p2962 p3097 p4110 p4539 : Prop)
    (h40810 : (¬ p2027))
    (h28330 : p2027 ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4539))
    : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28330 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54566 (p1992 p2027 p2202 p2608 p3641 p3684 p3860 p4370 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28337 : (¬ p1992) ∨ p2027 ∨ p2202 ∨ (¬ p2608) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3860) ∨ (¬ p4370))
    : (¬ p2608) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3860) ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h28337 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54568 (p1994 p2027 p2323 p2440 p2946 p3156 p3880 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h28339 : (¬ p1994) ∨ p2027 ∨ p2323 ∨ (¬ p2440) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880))
    : (¬ p2440) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h28339 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54572 (p1981 p2027 p2247 p2352 p2493 p2688 p3379 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h28343 : (¬ p1981) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2493) ∨ p2688 ∨ (¬ p3379))
    : (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h28343 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54575 (p2027 p2254 p2363 p2608 p2839 p3105 p3172 p4118 p4335 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h28348 : p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4335) ∨ (¬ p4433))
    : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4335) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28348 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54578 (p2027 p2156 p2187 p2363 p2608 p3370 p3452 p3590 p4377 p4697 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h28352 : p2027 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4377) ∨ (¬ p4697) ∨ (¬ p5160))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4377) ∨ (¬ p4697) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28352 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54579 (p2027 p2307 p3055 p3319 p3549 p3684 p4368 p4736 p4948 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h28353 : p2027 ∨ (¬ p2307) ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3684) ∨ (¬ p4368) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5020))
    : (¬ p2307) ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3684) ∨ (¬ p4368) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28353 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54580 (p1985 p2027 p2449 p2807 p3042 p3172 p3690 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40892 : (¬ p3042))
    (h28355 : (¬ p1985) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p2807) ∨ p3042 ∨ (¬ p3172) ∨ (¬ p3690))
    : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3042) := h40892;
    (Or.elim h28355 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54583 (p2027 p3946 p3998 p4114 p4186 p4286 p4620 p4710 : Prop)
    (h40810 : (¬ p2027))
    (h28365 : p2027 ∨ (¬ p3946) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4620) ∨ (¬ p4710))
    : (¬ p3946) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4620) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28365 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54587 (p2027 p2870 p2881 p3553 p4386 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h28369 : p2027 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4386) ∨ (¬ p5053))
    : (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4386) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28369 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54595 (p2027 p2299 p3097 p3379 p3641 p3645 p3646 p3954 p4030 p4420 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h28379 : p2027 ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4420) ∨ (¬ p4877))
    : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4420) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28379 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54599 (p1986 p2027 p2553 p2598 p2780 p3008 p3822 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h28384 : (¬ p1986) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2780) ∨ p3008 ∨ (¬ p3822))
    : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h28384 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54601 (p1977 p2027 p2241 p2553 p3008 p3568 p3591 p4319 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h28386 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p4319))
    : (¬ p2241) ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p3591) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h28386 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54604 (p2027 p2668 p2696 p2797 p3238 p3452 p3880 p4134 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28389 : p2027 ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4733))
    : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28389 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54607 (p2027 p2891 p3568 p4140 p4173 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h28394 : p2027 ∨ (¬ p2891) ∨ (¬ p3568) ∨ (¬ p4140) ∨ (¬ p4173) ∨ (¬ p4564))
    : (¬ p2891) ∨ (¬ p3568) ∨ (¬ p4140) ∨ (¬ p4173) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28394 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54608 (p2027 p2248 p2807 p3238 p3256 p3452 p3880 p4044 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h28395 : p2027 ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3238) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3238) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28395 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54609 (p1994 p2027 p2528 p2630 p3177 p3498 p3857 p3877 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h28396 : (¬ p1994) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p3177) ∨ p3498 ∨ (¬ p3857) ∨ (¬ p3877))
    : (¬ p2528) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p3877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3498) := h40899;
    (Or.elim h28396 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54610 (p2027 p2245 p2406 p2509 p2589 p2655 p3471 p3609 p4348 p4438 p4733 p4805 : Prop)
    (h40810 : (¬ p2027))
    (h28397 : p2027 ∨ (¬ p2245) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3471) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4733) ∨ (¬ p4805))
    : (¬ p2245) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3471) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4733) ∨ (¬ p4805) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28397 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54614 (p2027 p2588 p3276 p4191 p4422 p4624 : Prop)
    (h40810 : (¬ p2027))
    (h28401 : p2027 ∨ (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4624))
    : (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28401 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54618 (p1976 p2027 p2169 p3055 p3309 p3822 p3923 p5220 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28407 : (¬ p1976) ∨ p2027 ∨ p2169 ∨ (¬ p3055) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3923) ∨ (¬ p5220))
    : (¬ p3055) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3923) ∨ (¬ p5220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h28407 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54620 (p2027 p2630 p2922 p3361 p3414 p3740 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h28410 : p2027 ∨ (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4814))
    : (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28410 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54627 (p2027 p2363 p2383 p3055 p3266 p3876 p3987 p4786 p4831 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h28418 : p2027 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28418 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54629 (p2027 p2577 p3389 p3564 p3660 p3946 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h28420 : p2027 ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3946) ∨ (¬ p4646))
    : (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3946) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54630 (p2027 p2132 p2579 p2619 p2753 p3146 p3324 p3347 p3984 p5118 p5216 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h28421 : p2027 ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p3347) ∨ (¬ p3984) ∨ (¬ p5118) ∨ (¬ p5216) ∨ (¬ p5580))
    : (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p3347) ∨ (¬ p3984) ∨ (¬ p5118) ∨ (¬ p5216) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28421 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54631 (p2027 p2254 p2608 p2707 p2963 p4037 p4191 p4253 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h28423 : p2027 ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4826))
    : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28423 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54633 (p2027 p2655 p3136 p3156 p3904 p4120 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h28425 : p2027 ∨ (¬ p2655) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4787))
    : (¬ p2655) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28425 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54639 (p2027 p2247 p2459 p2881 p3051 p4037 p4154 p4521 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h28432 : p2027 ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p4604))
    : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28432 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54645 (p2027 p2156 p2274 p2396 p2696 p3370 p3425 p3659 p4418 p4668 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h28439 : p2027 ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (¬ p3370) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4418) ∨ (¬ p4668) ∨ (¬ p5049))
    : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (¬ p3370) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4418) ∨ (¬ p4668) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28439 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54649 (p1987 p2545 p2751 p4111 : Prop)
    (h2147 : p1987)
    (h40876 : (¬ p2545))
    (h28444 : (¬ p1987) ∨ p2545 ∨ p2751 ∨ (¬ p4111))
    : p2751 ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2751) := (fun h => hn (Or.inl h));
    let u1 : p4111 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p1987 := h2147;
    let u3 : (¬ p2545) := h40876;
    (Or.elim h28444 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step54653 (p1979 p2027 p2766 p2860 p3692 p3694 p3952 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28449 : (¬ p1979) ∨ p2027 ∨ p2766 ∨ (¬ p2860) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3952))
    : (¬ p2860) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h28449 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54654 (p1979 p2027 p2156 p2766 p3692 p3952 p4120 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28450 : (¬ p1979) ∨ p2027 ∨ (¬ p2156) ∨ p2766 ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4120))
    : (¬ p2156) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h28450 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54659 (p2027 p2245 p2657 p2727 p2749 p3093 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h28456 : p2027 ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3093) ∨ (¬ p4870))
    : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p3093) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28456 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54661 (p2010 p2027 p2247 p2437 p2688 p3232 p3359 p3830 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h28458 : (¬ p2010) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2437) ∨ p2688 ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830))
    : (¬ p2247) ∨ (¬ p2437) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h28458 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54664 (p2027 p3005 p4311 p4315 p5569 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h28461 : p2027 ∨ (¬ p3005) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p5569) ∨ (¬ p5740))
    : (¬ p3005) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p5569) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54667 (p2027 p2341 p2589 p3553 p3984 p4067 p4717 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h28466 : p2027 ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3553) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3553) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28466 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54669 (p1977 p2027 p2331 p2764 p3292 p4154 p5284 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h28469 : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2764 ∨ (¬ p3292) ∨ (¬ p4154) ∨ (¬ p5284))
    : (¬ p2331) ∨ (¬ p3292) ∨ (¬ p4154) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h28469 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54672 (p2022 p3551 p3578 p4905 : Prop)
    (h2182 : p2022)
    (h40900 : (¬ p3578))
    (h28472 : (¬ p2022) ∨ (¬ p3551) ∨ p3578 ∨ p4905)
    : (¬ p3551) ∨ p4905 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3551 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4905) := (fun h => hn (Or.inr h));
    let u2 : p2022 := h2182;
    let u3 : (¬ p3578) := h40900;
    (Or.elim h28472 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step54673 (p1983 p2027 p2449 p2696 p2699 p2707 p2743 p3589 p4325 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28473 : (¬ p1983) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p2696) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3589) ∨ (¬ p4325))
    : (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3589) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h28473 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54674 (p1990 p2027 p2241 p2284 p2699 p2891 p4320 p4365 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28474 : (¬ p1990) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2284) ∨ p2699 ∨ (¬ p2891) ∨ (¬ p4320) ∨ (¬ p4365))
    : (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2891) ∨ (¬ p4320) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28474 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54676 (p2027 p2241 p2641 p3323 p3540 p3644 p4330 p4348 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h28477 : p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28477 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54680 (p2027 p2922 p3193 p3246 p4264 p4277 p5295 : Prop)
    (h40810 : (¬ p2027))
    (h28481 : p2027 ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p4264) ∨ (¬ p4277) ∨ (¬ p5295))
    : (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p4264) ∨ (¬ p4277) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28481 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54688 (p1982 p2027 p2114 p2363 p2518 p3379 p3954 p4157 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28490 : (¬ p1982) ∨ p2027 ∨ p2114 ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4157))
    : (¬ p2363) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h28490 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54692 (p2027 p2191 p2774 p2819 p3555 p3692 p3979 p4733 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h28494 : p2027 ∨ (¬ p2191) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p5122))
    : (¬ p2191) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28494 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54698 (p2027 p2252 p2476 p2534 p2655 p2750 p3146 p3399 p3527 p3954 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h28501 : p2027 ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3146) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4905))
    : (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3146) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28501 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54699 (p2027 p2532 p3105 p3694 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h28502 : p2027 ∨ (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28502 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54703 (p2008 p2027 p2737 p3365 p3471 p3474 p3583 : Prop)
    (h2168 : p2008)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h28508 : (¬ p2008) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) ∨ p3474 ∨ (¬ p3583))
    : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3583) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2008 := h2168;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h28508 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54704 (p2027 p2156 p3115 p3588 p3952 p3954 p4106 p4278 p4521 p4621 p5045 : Prop)
    (h40810 : (¬ p2027))
    (h28509 : p2027 ∨ (¬ p2156) ∨ (¬ p3115) ∨ (¬ p3588) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4278) ∨ (¬ p4521) ∨ (¬ p4621) ∨ (¬ p5045))
    : (¬ p2156) ∨ (¬ p3115) ∨ (¬ p3588) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4278) ∨ (¬ p4521) ∨ (¬ p4621) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28509 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54706 (p2027 p2563 p2668 p3745 p4235 p4275 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h28511 : p2027 ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3745) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4405))
    : (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3745) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28511 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54707 (p2027 p2417 p3051 p4032 p4382 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h28512 : p2027 ∨ (¬ p2417) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4647))
    : (¬ p2417) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28512 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54710 (p1985 p2027 p2138 p2177 p2307 p2786 p3474 p3570 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h28515 : (¬ p1985) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2786) ∨ p3474 ∨ (¬ p3570))
    : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3474) := h40898;
    (Or.elim h28515 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54712 (p2027 p2248 p2901 p2946 p3193 p3452 p4129 p4425 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h28520 : p2027 ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826))
    : (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28520 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54713 (p2027 p2122 p2132 p2476 p3083 p3097 p3574 p3589 p3985 p4718 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h28521 : p2027 ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p3589) ∨ (¬ p3985) ∨ (¬ p4718) ∨ (¬ p5193))
    : (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p3589) ∨ (¬ p3985) ∨ (¬ p4718) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28521 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54716 (p2027 p2210 p2254 p2963 p2972 p3324 p3680 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h28525 : p2027 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p2972) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p2972) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28525 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54722 (p2011 p2027 p2241 p2699 p2992 p3506 p4322 p5038 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28531 : (¬ p2011) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2992) ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p5038))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p5038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2011 := h2171;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28531 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54726 (p2027 p2619 p3051 p4120 p4235 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h28536 : p2027 ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4885))
    : (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28536 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54732 (p2027 p2573 p2663 p2952 p3574 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h28544 : p2027 ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3574) ∨ (¬ p4701))
    : (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3574) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28544 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54734 (p1998 p2027 p2220 p2622 p2951 p3136 p3146 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28547 : (¬ p1998) ∨ p2027 ∨ (¬ p2220) ∨ p2622 ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p4348))
    : (¬ p2220) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h28547 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54737 (p1987 p2027 p2169 p2651 p2810 p2963 p3324 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28550 : (¬ p1987) ∨ p2027 ∨ p2169 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3324))
    : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h28550 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54740 (p2027 p2104 p2264 p2807 p4117 p4807 : Prop)
    (h40810 : (¬ p2027))
    (h28556 : p2027 ∨ (¬ p2104) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p4807))
    : (¬ p2104) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p4807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28556 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54741 (p2027 p2192 p3146 p4261 p4492 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h28557 : p2027 ∨ (¬ p2192) ∨ (¬ p3146) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4507))
    : (¬ p2192) ∨ (¬ p3146) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28557 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54744 (p2027 p2406 p2589 p2655 p2807 p4116 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h28560 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4116) ∨ (¬ p4652))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4116) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54753 (p1984 p2027 p2247 p2545 p2797 p2810 p4154 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28575 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ p2545 ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4154))
    : (¬ p2247) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h28575 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54755 (p2027 p2138 p3471 p4173 p4243 p4344 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28577 : p2027 ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4344) ∨ (¬ p4558))
    : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4344) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28577 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54756 (p2027 p2476 p2936 p3389 p3527 p4383 : Prop)
    (h40810 : (¬ p2027))
    (h28578 : p2027 ∨ (¬ p2476) ∨ (¬ p2936) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p4383))
    : (¬ p2476) ∨ (¬ p2936) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2936 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28578 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54758 (p2027 p2104 p2187 p2774 p4857 p4889 : Prop)
    (h40810 : (¬ p2027))
    (h28580 : p2027 ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p4857) ∨ (¬ p4889))
    : (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p4857) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28580 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54759 (p2027 p2177 p2553 p2573 p3954 p4242 p4324 p4666 p4805 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h28581 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4324) ∨ (¬ p4666) ∨ (¬ p4805) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4324) ∨ (¬ p4666) ∨ (¬ p4805) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28581 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54760 (p2027 p2743 p2810 p3537 p4967 p5011 : Prop)
    (h40810 : (¬ p2027))
    (h28582 : p2027 ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5011))
    : (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28582 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54763 (p1990 p2027 p2545 p2641 p2668 p3989 p4111 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28585 : (¬ p1990) ∨ p2027 ∨ p2545 ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4111))
    : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h28585 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54765 (p2027 p2295 p3019 p3189 p3549 p4245 p5011 : Prop)
    (h40810 : (¬ p2027))
    (h28587 : p2027 ∨ (¬ p2295) ∨ (¬ p3019) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p5011))
    : (¬ p2295) ∨ (¬ p3019) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28587 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54769 (p2027 p2417 p2437 p3686 p4324 p4750 : Prop)
    (h40810 : (¬ p2027))
    (h28591 : p2027 ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4324) ∨ (¬ p4750))
    : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4324) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54771 (p1987 p2027 p3146 p3661 p3982 p4118 p4315 p5568 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h28593 : (¬ p1987) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3661) ∨ p3982 ∨ (¬ p4118) ∨ (¬ p4315) ∨ (¬ p5568))
    : (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4315) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3982) := h40909;
    (Or.elim h28593 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54773 (p2027 p2122 p2143 p3097 p3985 p4032 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h28595 : p2027 ∨ (¬ p2122) ∨ (¬ p2143) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4032) ∨ (¬ p5043))
    : (¬ p2122) ∨ (¬ p2143) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4032) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28595 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54774 (p1990 p2027 p2156 p2166 p2938 p4120 p4244 p4418 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h28597 : (¬ p1990) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2166) ∨ p2938 ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4418))
    : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h28597 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54776 (p1986 p2027 p2230 p2476 p2534 p2766 p3684 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28601 : (¬ p1986) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ p2766 ∨ (¬ p3684))
    : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h28601 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54780 (p1990 p2027 p2169 p2191 p2192 p2363 p3857 p4115 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28605 : (¬ p1990) ∨ p2027 ∨ p2169 ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4115))
    : (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h28605 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54781 (p2027 p2187 p3093 p3860 p4514 p4993 : Prop)
    (h40810 : (¬ p2027))
    (h28606 : p2027 ∨ (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p4993))
    : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p4993) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54784 (p2027 p2177 p2254 p2608 p3201 p3367 p3414 p3553 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h28612 : p2027 ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4276))
    : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28612 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54785 (p2018 p2027 p2088 p2437 p2482 p2545 p3540 p4340 : Prop)
    (h2178 : p2018)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28613 : (¬ p2018) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2437) ∨ (¬ p2482) ∨ p2545 ∨ (¬ p3540) ∨ (¬ p4340))
    : (¬ p2088) ∨ (¬ p2437) ∨ (¬ p2482) ∨ (¬ p3540) ∨ (¬ p4340) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2018 := h2178;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h28613 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54787 (p2027 p3055 p3516 p3819 p4324 p4357 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h28615 : p2027 ∨ (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4749))
    : (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28615 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54791 (p1982 p2027 p2098 p2136 p2363 p2860 p3474 p3646 p4326 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h28620 : (¬ p1982) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p2136) ∨ (¬ p2363) ∨ (¬ p2860) ∨ p3474 ∨ (¬ p3646) ∨ (¬ p4326))
    : (¬ p2098) ∨ (¬ p2136) ∨ (¬ p2363) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4326) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1982 := h2142;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3474) := h40898;
    (Or.elim h28620 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54793 (p2027 p2088 p2484 p3266 p4045 p4425 : Prop)
    (h40810 : (¬ p2027))
    (h28622 : p2027 ∨ (¬ p2088) ∨ (¬ p2484) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4425))
    : (¬ p2088) ∨ (¬ p2484) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2484 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28622 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54795 (p2027 p2387 p2459 p2518 p3204 p3379 p3954 p4347 p4420 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h28624 : p2027 ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (¬ p3204) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4420) ∨ (¬ p4870))
    : (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (¬ p3204) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4420) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28624 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54803 (p2027 p2662 p2810 p3136 p3540 p4241 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h28634 : p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3540) ∨ (¬ p4241) ∨ (¬ p4644))
    : (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3540) ∨ (¬ p4241) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28634 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54811 (p2027 p2220 p2249 p2656 p2727 p3146 p3292 p3461 p4399 p4604 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h28644 : p2027 ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3146) ∨ (¬ p3292) ∨ (¬ p3461) ∨ (¬ p4399) ∨ (¬ p4604) ∨ (¬ p5284))
    : (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3146) ∨ (¬ p3292) ∨ (¬ p3461) ∨ (¬ p4399) ∨ (¬ p4604) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28644 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54815 (p2027 p2252 p2396 p2750 p3292 p3399 p3547 p3680 p3951 p3954 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h28649 : p2027 ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3680) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p5284))
    : (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3680) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28649 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54816 (p2027 p2598 p2780 p3016 p4342 p4750 : Prop)
    (h40810 : (¬ p2027))
    (h28650 : p2027 ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750))
    : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28650 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54817 (p2027 p2098 p2743 p2963 p3324 p3361 p3609 p4348 p4503 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h28651 : p2027 ∨ (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4737))
    : (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28651 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54819 (p2027 p3631 p3687 p3688 p4324 p4357 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h28653 : p2027 ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3688) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4842))
    : (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3688) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28653 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54820 (p2027 p2839 p2860 p4242 p4507 p4740 : Prop)
    (h40810 : (¬ p2027))
    (h28654 : p2027 ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4242) ∨ (¬ p4507) ∨ (¬ p4740))
    : (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4242) ∨ (¬ p4507) ∨ (¬ p4740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28654 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54822 (p2006 p2027 p2764 p2901 p4208 p4244 p4322 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h28656 : (¬ p2006) ∨ p2027 ∨ p2764 ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4244) ∨ (¬ p4322))
    : (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4244) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2006 := h2166;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h28656 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54823 (p1988 p2027 p2441 p3146 p3222 p3276 p3347 p3578 p3584 p3685 p3759 p4253 p4340 p4715 p5503 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h28657 : (¬ p1988) ∨ p2027 ∨ (¬ p2441) ∨ (¬ p3146) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3347) ∨ p3578 ∨ (¬ p3584) ∨ (¬ p3685) ∨ (¬ p3759) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p4715) ∨ (¬ p5503))
    : (¬ p2441) ∨ (¬ p3146) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3347) ∨ (¬ p3584) ∨ (¬ p3685) ∨ (¬ p3759) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p4715) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p1988 := h2148;
    let u13 : (¬ p2027) := h40810;
    let u14 : (¬ p3578) := h40900;
    (Or.elim h28657 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u14 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u9))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u10))) (fun r13 => (False.elim (r13 u11)))))))))))))))))))))))))))))))

theorem step54826 (p2027 p2252 p2352 p2363 p2573 p2741 p3292 p3519 p3680 p4376 p5059 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h28661 : p2027 ∨ (¬ p2252) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2741) ∨ (¬ p3292) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4376) ∨ (¬ p5059) ∨ (¬ p5284))
    : (¬ p2252) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2741) ∨ (¬ p3292) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4376) ∨ (¬ p5059) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28661 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54831 (p1998 p2027 p2156 p2699 p2881 p2891 p4172 p4173 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28666 : (¬ p1998) ∨ p2027 ∨ (¬ p2156) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4172) ∨ (¬ p4173))
    : (¬ p2156) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4172) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28666 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54832 (p2027 p2132 p2166 p2743 p3146 p3361 p3414 p3947 p4418 p4669 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h28667 : p2027 ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4418) ∨ (¬ p4669) ∨ (¬ p4737))
    : (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4418) ∨ (¬ p4669) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28667 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54833 (p2027 p3201 p3868 p4067 p4194 p4391 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h28670 : p2027 ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4067) ∨ (¬ p4194) ∨ (¬ p4391) ∨ (¬ p4753))
    : (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4067) ∨ (¬ p4194) ∨ (¬ p4391) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28670 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54835 (p1976 p2027 p2589 p2764 p2850 p3905 p4425 p5160 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h28672 : (¬ p1976) ∨ p2027 ∨ (¬ p2589) ∨ p2764 ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160))
    : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h28672 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54841 (p2027 p2230 p2246 p2440 p2531 p2608 p2663 p2744 p3083 p3548 p4366 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h28678 : p2027 ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4902))
    : (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28678 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54849 (p1976 p2027 p2313 p2633 p2778 p3553 p3931 p4260 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28688 : (¬ p1976) ∨ p2027 ∨ (¬ p2313) ∨ p2633 ∨ (¬ p2778) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p4260))
    : (¬ p2313) ∨ (¬ p2778) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p4260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h28688 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54853 (p2027 p2881 p3051 p3365 p3366 p3370 p3941 p4035 p4377 p5119 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h28692 : p2027 ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p4377) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p4377) ∨ (¬ p5119) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28692 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54862 (p2027 p2274 p2313 p2383 p3324 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h28705 : p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p4564))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28705 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54864 (p2027 p2248 p2534 p2651 p3256 p3486 p3555 p3570 p4121 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h28707 : p2027 ∨ (¬ p2248) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4121) ∨ (¬ p4420))
    : (¬ p2248) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4121) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28707 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54867 (p2027 p2352 p2363 p2573 p2952 p3136 p3366 p3519 p4035 p4236 p4376 p5113 : Prop)
    (h40810 : (¬ p2027))
    (h28711 : p2027 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28711 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54869 (p2027 p2210 p2870 p4366 p4875 p4909 : Prop)
    (h40810 : (¬ p2027))
    (h28714 : p2027 ∨ (¬ p2210) ∨ (¬ p2870) ∨ (¬ p4366) ∨ (¬ p4875) ∨ (¬ p4909))
    : (¬ p2210) ∨ (¬ p2870) ∨ (¬ p4366) ∨ (¬ p4875) ∨ (¬ p4909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28714 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54870 (p2027 p2579 p2819 p3956 p4375 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h28715 : p2027 ∨ (¬ p2579) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4727))
    : (¬ p2579) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28715 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54871 (p1976 p2027 p2579 p2764 p3422 p3905 p4425 p5160 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h28716 : (¬ p1976) ∨ p2027 ∨ (¬ p2579) ∨ p2764 ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160))
    : (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h28716 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54872 (p1988 p2027 p2363 p3266 p3449 p3591 p3818 p4318 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40905 : (¬ p3818))
    (h28719 : (¬ p1988) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3591) ∨ p3818 ∨ (¬ p4318))
    : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3818) := h40905;
    (Or.elim h28719 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54875 (p1984 p2027 p2138 p2633 p2839 p3570 p3588 p3873 p4169 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28722 : (¬ p1984) ∨ p2027 ∨ (¬ p2138) ∨ p2633 ∨ (¬ p2839) ∨ (¬ p3570) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4169))
    : (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3570) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4169) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h28722 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54876 (p1975 p2027 p2295 p2331 p2622 p2630 p2657 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28723 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2331) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2657))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2630) ∨ (¬ p2657) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h28723 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54878 (p1997 p2027 p2406 p2764 p3347 p3540 p4278 p4381 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h28725 : (¬ p1997) ∨ p2027 ∨ (¬ p2406) ∨ p2764 ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381))
    : (¬ p2406) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h28725 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54879 (p1990 p2027 p2563 p2611 p2946 p4117 p4272 p5433 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h28727 : (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ p2611 ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433))
    : (¬ p2563) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4272 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h28727 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54880 (p1997 p2027 p2619 p2622 p2743 p2839 p3880 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h28728 : (¬ p1997) ∨ p2027 ∨ (¬ p2619) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3880))
    : (¬ p2619) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h28728 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54881 (p2027 p2891 p3136 p3572 p3691 p4155 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h28729 : p2027 ∨ (¬ p2891) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p4960))
    : (¬ p2891) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28729 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54882 (p2027 p2122 p2839 p3549 p3953 p4426 p5052 : Prop)
    (h40810 : (¬ p2027))
    (h28730 : p2027 ∨ (¬ p2122) ∨ (¬ p2839) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4426) ∨ (¬ p5052))
    : (¬ p2122) ∨ (¬ p2839) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4426) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28730 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54883 (p2027 p2274 p2829 p3588 p3958 p4390 p4471 : Prop)
    (h40810 : (¬ p2027))
    (h28731 : p2027 ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p3958) ∨ (¬ p4390) ∨ (¬ p4471))
    : (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p3958) ∨ (¬ p4390) ∨ (¬ p4471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28731 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54884 (p2027 p2386 p3609 p3684 p3857 p4197 p4354 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h28732 : p2027 ∨ (¬ p2386) ∨ (¬ p3609) ∨ (¬ p3684) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4354) ∨ (¬ p4717))
    : (¬ p2386) ∨ (¬ p3609) ∨ (¬ p3684) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4354) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28732 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54885 (p2027 p2248 p2901 p2946 p3246 p3591 p3923 p3950 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h28734 : p2027 ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347))
    : (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28734 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54888 (p1995 p2027 p2534 p3146 p3379 p3578 p3860 p4370 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h28737 : (¬ p1995) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3379) ∨ p3578 ∨ (¬ p3860) ∨ (¬ p4370))
    : (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h28737 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54889 (p2027 p2132 p2363 p2870 p2881 p3591 p4261 p4371 p4503 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28738 : p2027 ∨ (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3591) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3591) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4503) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28738 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54891 (p2027 p2396 p2668 p3947 p4067 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h28741 : p2027 ∨ (¬ p2396) ∨ (¬ p2668) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405))
    : (¬ p2396) ∨ (¬ p2668) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28741 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54892 (p2027 p2145 p3266 p3343 p3362 p3389 p3742 p4120 p4322 p4332 p4335 : Prop)
    (h40810 : (¬ p2027))
    (h28742 : p2027 ∨ (¬ p2145) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335))
    : (¬ p2145) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28742 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54894 (p2027 p2797 p3986 p4208 p4315 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h28744 : p2027 ∨ (¬ p2797) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5043))
    : (¬ p2797) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28744 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54897 (p2027 p2145 p2264 p2459 p2563 p2807 p3646 p4117 p4948 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h28748 : p2027 ∨ (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28748 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54899 (p2027 p3670 p4322 p4363 p4875 p5031 : Prop)
    (h40810 : (¬ p2027))
    (h28750 : p2027 ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4875) ∨ (¬ p5031))
    : (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4875) ∨ (¬ p5031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28750 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54904 (p2027 p3105 p3570 p4135 p4244 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h28756 : p2027 ∨ (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4668))
    : (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28756 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54905 (p2027 p2241 p2352 p2387 p2449 p3027 p4137 p4625 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h28758 : p2027 ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5021))
    : (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28758 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54909 (p2027 p2641 p3125 p3848 p4190 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h28762 : p2027 ∨ (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3848) ∨ (¬ p4190) ∨ (¬ p4564))
    : (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3848) ∨ (¬ p4190) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28762 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54910 (p1992 p2027 p2177 p2311 p2462 p2785 p3551 p3688 p4107 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h28763 : (¬ p1992) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ p2462 ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2462) := h40875;
    (Or.elim h28763 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54911 (p2027 p2138 p2190 p2247 p2744 p3063 p3093 p3097 p3366 p3694 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h28764 : p2027 ∨ (¬ p2138) ∨ (¬ p2190) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3694) ∨ (¬ p4405))
    : (¬ p2138) ∨ (¬ p2190) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3694) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28764 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54913 (p2027 p2911 p2922 p3097 p3379 p3646 p4107 p4524 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h28766 : p2027 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28766 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54914 (p2005 p2027 p3016 p3128 p3359 p3461 p4425 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h28767 : (¬ p2005) ∨ p2027 ∨ (¬ p3016) ∨ p3128 ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p4425))
    : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3128) := h40894;
    (Or.elim h28767 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54915 (p2027 p2138 p2437 p2651 p3868 p4322 p4385 p4786 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h28768 : p2027 ∨ (¬ p2138) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p4826))
    : (¬ p2138) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4786) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28768 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54916 (p1992 p2027 p2766 p3266 p3346 p3363 p3585 p4425 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28770 : (¬ p1992) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4425))
    : (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h28770 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54918 (p1987 p2027 p2534 p2651 p2766 p2810 p3172 p4437 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28773 : (¬ p1987) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2651) ∨ p2766 ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4437))
    : (¬ p2534) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h28773 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54919 (p1983 p2027 p2247 p2688 p3707 p3830 p4381 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h28774 : (¬ p1983) ∨ p2027 ∨ (¬ p2247) ∨ p2688 ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4381))
    : (¬ p2247) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h28774 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54921 (p2027 p2191 p2668 p2696 p2753 p2797 p3379 p3555 p4134 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h28778 : p2027 ∨ (¬ p2191) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4134) ∨ (¬ p5216))
    : (¬ p2191) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4134) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28778 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54923 (p2027 p2122 p2589 p2774 p3791 p4322 p4729 p4826 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h28780 : p2027 ∨ (¬ p2122) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948))
    : (¬ p2122) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28780 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54926 (p2027 p2589 p2685 p2696 p3931 p4322 p4729 p4826 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h28783 : p2027 ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948))
    : (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28783 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54927 (p1984 p2027 p2633 p3246 p3570 p3817 p4366 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28784 : (¬ p1984) ∨ p2027 ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3817) ∨ (¬ p4366))
    : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3817) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h28784 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54929 (p2027 p2190 p2901 p3146 p3661 p4118 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28786 : p2027 ∨ (¬ p2190) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4558))
    : (¬ p2190) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28786 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54930 (p1994 p2027 p2352 p2387 p2630 p2667 p3008 p4195 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h28787 : (¬ p1994) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2667) ∨ p3008 ∨ (¬ p4195))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2667) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h28787 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54932 (p1983 p2027 p2202 p2396 p2563 p3051 p3646 p4140 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28789 : (¬ p1983) ∨ p2027 ∨ p2202 ∨ (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140))
    : (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h28789 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54935 (p2027 p2136 p2619 p3471 p4120 p4897 : Prop)
    (h40810 : (¬ p2027))
    (h28795 : p2027 ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p3471) ∨ (¬ p4120) ∨ (¬ p4897))
    : (¬ p2136) ∨ (¬ p2619) ∨ (¬ p3471) ∨ (¬ p4120) ∨ (¬ p4897) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4897 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28795 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54937 (p2027 p2246 p2608 p2744 p2901 p2946 p3193 p3246 p3452 p4641 : Prop)
    (h40810 : (¬ p2027))
    (h28799 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4641))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28799 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54941 (p1977 p2027 p2191 p2241 p2766 p3555 p3692 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28803 : (¬ p1977) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2241) ∨ p2766 ∨ (¬ p3555) ∨ (¬ p3692))
    : (¬ p2191) ∨ (¬ p2241) ∨ (¬ p3555) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h28803 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54942 (p1998 p2027 p2202 p2563 p2881 p2891 p3645 p3646 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28804 : (¬ p1998) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3645) ∨ (¬ p3646))
    : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3645) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h28804 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54943 (p1998 p2027 p2202 p2563 p2881 p3051 p3646 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28805 : (¬ p1998) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646))
    : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h28805 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54947 (p2027 p2220 p2870 p3646 p3694 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h28810 : p2027 ∨ (¬ p2220) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p4558))
    : (¬ p2220) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28810 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54949 (p2027 p2104 p3366 p3399 p3452 p4075 p4340 p4376 p4444 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h28812 : p2027 ∨ (¬ p2104) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826))
    : (¬ p2104) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28812 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54950 (p2027 p3172 p3366 p3399 p3452 p4075 p4236 p4340 p4376 p4444 p4826 p4967 : Prop)
    (h40810 : (¬ p2027))
    (h28813 : p2027 ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4236) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4967))
    : (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4236) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4967) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h28813 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step54957 (p1990 p2027 p2307 p2545 p2810 p3097 p3136 p3567 p4336 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h28820 : (¬ p1990) ∨ p2027 ∨ (¬ p2307) ∨ p2545 ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336))
    : (¬ p2307) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2545) := h40876;
    (Or.elim h28820 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54958 (p2027 p2264 p2274 p3956 p4138 p4203 p4361 : Prop)
    (h40810 : (¬ p2027))
    (h28822 : p2027 ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4203) ∨ (¬ p4361))
    : (¬ p2264) ∨ (¬ p2274) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4203) ∨ (¬ p4361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28822 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54959 (p1975 p2027 p2202 p2417 p2589 p3389 p4107 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28823 : (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4107))
    : (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h28823 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54961 (p2027 p2341 p2641 p2656 p3031 p3548 p4975 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h28825 : p2027 ∨ (¬ p2341) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4975) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4975) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h28825 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54964 (p2027 p2254 p2417 p2598 p2963 p3201 p3324 p3589 p3950 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h28828 : p2027 ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p3589) ∨ (¬ p3950) ∨ (¬ p4347))
    : (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p3589) ∨ (¬ p3950) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28828 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54966 (p1982 p2027 p2608 p2699 p3537 p3670 p4444 p5344 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28832 : (¬ p1982) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p3537) ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p5344))
    : (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p5344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28832 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54967 (p1991 p2027 p2534 p2630 p2657 p2766 p3877 p4437 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28834 : (¬ p1991) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2657) ∨ p2766 ∨ (¬ p3877) ∨ (¬ p4437))
    : (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1991 := h2151;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h28834 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54970 (p2027 p2137 p2156 p2748 p2839 p3125 p3365 p4118 p4330 p4360 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h28837 : p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4734))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28837 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54978 (p2027 p3051 p3367 p3486 p3759 p4399 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h28850 : p2027 ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3759) ∨ (¬ p4399) ∨ (¬ p4877))
    : (¬ p3051) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3759) ∨ (¬ p4399) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28850 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54983 (p2027 p2619 p3696 p3758 p3956 p3958 p4113 : Prop)
    (h40810 : (¬ p2027))
    (h28855 : p2027 ∨ (¬ p2619) ∨ (¬ p3696) ∨ (¬ p3758) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4113))
    : (¬ p2619) ∨ (¬ p3696) ∨ (¬ p3758) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4113) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28855 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54987 (p2027 p2590 p2797 p2810 p3238 p3984 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h28863 : p2027 ∨ (¬ p2590) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3984) ∨ (¬ p4811))
    : (¬ p2590) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3984) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28863 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54989 (p2027 p2088 p3819 p4242 p4340 p4590 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h28865 : p2027 ∨ (¬ p2088) ∨ (¬ p3819) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4590) ∨ (¬ p4737))
    : (¬ p2088) ∨ (¬ p3819) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4590) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28865 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54990 (p2027 p2210 p2780 p2891 p3246 p3950 p4347 p4358 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h28866 : p2027 ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736))
    : (¬ p2210) ∨ (¬ p2780) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28866 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54991 (p1980 p2027 p2241 p2699 p2797 p3027 p3572 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28867 : (¬ p1980) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2797) ∨ (¬ p3027) ∨ (¬ p3572))
    : (¬ p2241) ∨ (¬ p2797) ∨ (¬ p3027) ∨ (¬ p3572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h28867 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54992 (p2027 p2307 p2788 p3319 p3549 p3917 : Prop)
    (h40810 : (¬ p2027))
    (h28868 : p2027 ∨ (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3917))
    : (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2788 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28868 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54993 (p1977 p2027 p2534 p2651 p2766 p3172 p4111 p4437 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h28869 : (¬ p1977) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2651) ∨ p2766 ∨ (¬ p3172) ∨ (¬ p4111) ∨ (¬ p4437))
    : (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4111) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h28869 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54997 (p1981 p2027 p2187 p2210 p2699 p3097 p3309 p4338 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28873 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4338))
    : (¬ p2187) ∨ (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28873 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54998 (p1987 p2027 p2388 p2737 p2952 p3286 p4379 p5454 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h28874 : (¬ p1987) ∨ p2027 ∨ p2388 ∨ (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4379) ∨ (¬ p5454))
    : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4379) ∨ (¬ p5454) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h28874 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55005 (p2027 p2493 p2509 p2553 p4432 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h28882 : p2027 ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2553) ∨ (¬ p4432) ∨ (¬ p4501))
    : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2553) ∨ (¬ p4432) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28882 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55006 (p1979 p2027 p2177 p2992 p2996 p2997 p3551 p4155 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h28883 : (¬ p1979) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2992) ∨ (¬ p2996) ∨ p2997 ∨ (¬ p3551) ∨ (¬ p4155))
    : (¬ p2177) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h28883 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55011 (p2027 p2138 p2972 p3371 p4385 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h28888 : p2027 ∨ (¬ p2138) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p4385) ∨ (¬ p4734))
    : (¬ p2138) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p4385) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28888 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55014 (p2027 p2387 p2500 p3063 p3379 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h28891 : p2027 ∨ (¬ p2387) ∨ (¬ p2500) ∨ (¬ p3063) ∨ (¬ p3379) ∨ (¬ p5015))
    : (¬ p2387) ∨ (¬ p2500) ∨ (¬ p3063) ∨ (¬ p3379) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2500 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28891 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55022 (p1991 p2027 p2202 p2440 p3189 p3414 p3919 p4111 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h28899 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3189) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4111))
    : (¬ p2440) ∨ (¬ p3189) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1991 := h2151;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h28899 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55024 (p2027 p2248 p2499 p2946 p3256 p3452 p3692 p3956 p4237 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h28901 : p2027 ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4237) ∨ (¬ p4433))
    : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4237) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28901 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55025 (p2027 p2528 p3497 p3692 p4355 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h28902 : p2027 ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4702))
    : (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55028 (p2027 p2220 p2528 p3857 p4197 p4198 p4434 : Prop)
    (h40810 : (¬ p2027))
    (h28905 : p2027 ∨ (¬ p2220) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) ∨ (¬ p4434))
    : (¬ p2220) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28905 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55033 (p1988 p2027 p2114 p2449 p2737 p2761 p2807 p2811 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28910 : (¬ p1988) ∨ p2027 ∨ p2114 ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p2811))
    : (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p2811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h28910 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55037 (p2027 p2499 p3156 p3212 p3452 p3956 p4208 p4433 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h28916 : p2027 ∨ (¬ p2499) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4208) ∨ (¬ p4433) ∨ (¬ p4521))
    : (¬ p2499) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4208) ∨ (¬ p4433) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28916 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55042 (p1981 p2027 p2114 p2122 p2313 p2383 p2829 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28921 : (¬ p1981) ∨ p2027 ∨ p2114 ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h28921 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55044 (p2003 p2027 p2387 p2510 p2528 p2588 p2997 p4347 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h28923 : (¬ p2003) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p4347))
    : (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2003 := h2163;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h28923 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55049 (p1991 p2027 p2765 p2952 p2982 p4110 p4208 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h28930 : (¬ p1991) ∨ p2027 ∨ p2765 ∨ (¬ p2952) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208))
    : (¬ p2952) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h28930 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55051 (p2027 p2254 p2534 p2608 p2657 p2707 p3434 p3950 p4256 : Prop)
    (h40810 : (¬ p2027))
    (h28932 : p2027 ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28932 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55053 (p1990 p2027 p2169 p2284 p2498 p3319 p3956 p4033 p4208 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h28934 : (¬ p1990) ∨ p2027 ∨ p2169 ∨ (¬ p2284) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3956) ∨ (¬ p4033) ∨ (¬ p4208))
    : (¬ p2284) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3956) ∨ (¬ p4033) ∨ (¬ p4208) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2169) := h40866;
    (Or.elim h28934 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55054 (p2027 p2313 p2542 p2553 p2577 p2659 p3660 : Prop)
    (h40810 : (¬ p2027))
    (h28935 : p2027 ∨ (¬ p2313) ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3660))
    : (¬ p2313) ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28935 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55056 (p2027 p2132 p2528 p2870 p2881 p3452 p3453 p4261 p4438 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h28937 : p2027 ∨ (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28937 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55057 (p1984 p2027 p2247 p2287 p2630 p4111 p4195 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h28938 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ p2287 ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4195))
    : (¬ p2247) ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h28938 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55061 (p1990 p2027 p2699 p2860 p3073 p3449 p4340 p4359 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h28942 : (¬ p1990) ∨ p2027 ∨ p2699 ∨ (¬ p2860) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4340) ∨ (¬ p4359))
    : (¬ p2860) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4340) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h28942 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55065 (p2027 p2241 p3189 p3646 p3744 p4009 p4191 p4524 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h28950 : p2027 ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p5119))
    : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28950 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55069 (p1979 p2027 p2946 p2997 p3097 p3125 p3292 p4190 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h28954 : (¬ p1979) ∨ p2027 ∨ (¬ p2946) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4190))
    : (¬ p2946) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h28954 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55071 (p1981 p2027 p2114 p2307 p2352 p2584 p2588 p3367 p3759 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h28956 : (¬ p1981) ∨ p2027 ∨ p2114 ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1981 := h2141;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h28956 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55082 (p2027 p2459 p2641 p2668 p2696 p2742 p4133 p4242 p4340 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h28972 : p2027 ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p4133) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4737))
    : (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p4133) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h28972 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55084 (p2027 p2254 p2417 p2922 p2963 p3324 p3379 p3950 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h28976 : p2027 ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4347))
    : (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28976 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55085 (p1987 p2027 p2299 p2633 p2737 p3688 p3822 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28977 : (¬ p1987) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p3822))
    : (¬ p2299) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h28977 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55086 (p1987 p2027 p2299 p2313 p2633 p2737 p2785 p3688 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28978 : (¬ p1987) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ p2633 ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h28978 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55087 (p2012 p2027 p2881 p2938 p3548 p3707 p4425 p5363 : Prop)
    (h2172 : p2012)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h28979 : (¬ p2012) ∨ p2027 ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3548) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p5363))
    : (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p5363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2012 := h2172;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h28979 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55088 (p1987 p2027 p2287 p2696 p2780 p3323 p3917 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h28980 : (¬ p1987) ∨ p2027 ∨ p2287 ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3323) ∨ (¬ p3917))
    : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3323) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h28980 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55089 (p2027 p2254 p2518 p2528 p2952 p3379 p3744 p3952 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h28981 : p2027 ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604))
    : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h28981 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55090 (p1980 p2027 p2563 p2938 p3125 p4037 p4235 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h28982 : (¬ p1980) ∨ p2027 ∨ (¬ p2563) ∨ p2938 ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4235))
    : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h28982 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55092 (p2027 p2363 p3365 p3366 p3449 p3591 p4208 p4315 p4318 p4866 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h28984 : p2027 ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p5059))
    : (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h28984 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55098 (p2027 p2619 p3146 p3661 p4118 p4241 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h28990 : p2027 ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4241) ∨ (¬ p4885))
    : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4241) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h28990 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55100 (p2027 p2192 p2230 p2579 p3096 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h28992 : p2027 ∨ (¬ p2192) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4632))
    : (¬ p2192) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h28992 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55101 (p1979 p2027 p2409 p2493 p2657 p2946 p3574 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h28993 : (¬ p1979) ∨ p2027 ∨ p2409 ∨ (¬ p2493) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3574))
    : (¬ p2493) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h28993 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55106 (p1994 p2027 p2440 p2441 p2633 p3246 p3570 p4278 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h28999 : (¬ p1994) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2441) ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278))
    : (¬ p2440) ∨ (¬ p2441) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h28999 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55107 (p1994 p2027 p2633 p3246 p3570 p3742 p4278 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h29000 : (¬ p1994) ∨ p2027 ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4278))
    : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h29000 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55108 (p1995 p2027 p2441 p2633 p3238 p3246 p3570 p4278 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h29001 : (¬ p1995) ∨ p2027 ∨ (¬ p2441) ∨ p2633 ∨ (¬ p3238) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278))
    : (¬ p2441) ∨ (¬ p3238) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h29001 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55116 (p2027 p2177 p2307 p2440 p2459 p2657 p2781 p4236 p4948 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h29010 : p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29010 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55119 (p1986 p2027 p2241 p2437 p2699 p2727 p3876 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h29014 : (¬ p1986) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2437) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p3876))
    : (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h29014 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55122 (p1984 p2027 p2230 p2409 p2493 p2579 p2860 p2891 p3369 p3556 p4173 p4885 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h29023 : (¬ p1984) ∨ p2027 ∨ (¬ p2230) ∨ p2409 ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2860) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4885))
    : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2860) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1984 := h2144;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2409) := h40874;
    (Or.elim h29023 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u11 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step55123 (p1981 p2027 p2542 p2545 p2819 p2829 p3583 p3698 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29024 : (¬ p1981) ∨ p2027 ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3698))
    : (¬ p2542) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3698) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h29024 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55128 (p2027 p3073 p3662 p3859 p3878 p4118 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h29029 : p2027 ∨ (¬ p3073) ∨ (¬ p3662) ∨ (¬ p3859) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4701))
    : (¬ p3073) ∨ (¬ p3662) ∨ (¬ p3859) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29029 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55129 (p2027 p2651 p2901 p2950 p3556 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h29031 : p2027 ∨ (¬ p2651) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4701))
    : (¬ p2651) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29031 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55130 (p2027 p2589 p3093 p3319 p3347 p3692 p3880 p3954 p4330 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29032 : p2027 ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p5216))
    : (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29032 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55133 (p2027 p2190 p3146 p3324 p4347 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h29036 : p2027 ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4564))
    : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29036 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55138 (p2027 p2230 p2427 p2748 p3365 p3367 p3662 p3759 p3952 p4558 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h29042 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p3759) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p4734))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p3759) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29042 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55140 (p2027 p2137 p2156 p2187 p2839 p4436 p4998 : Prop)
    (h40810 : (¬ p2027))
    (h29044 : p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2839) ∨ (¬ p4436) ∨ (¬ p4998))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2839) ∨ (¬ p4436) ∨ (¬ p4998) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29044 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55144 (p1990 p2027 p2545 p2668 p2992 p3989 p4111 p4336 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29048 : (¬ p1990) ∨ p2027 ∨ p2545 ∨ (¬ p2668) ∨ (¬ p2992) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4336))
    : (¬ p2668) ∨ (¬ p2992) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h29048 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55146 (p2027 p2363 p3325 p3644 p3857 p4276 p4403 : Prop)
    (h40810 : (¬ p2027))
    (h29050 : p2027 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3857) ∨ (¬ p4276) ∨ (¬ p4403))
    : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3857) ∨ (¬ p4276) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29050 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55150 (p1984 p2027 p3146 p3578 p3583 p3954 p4340 p4359 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h29054 : (¬ p1984) ∨ p2027 ∨ (¬ p3146) ∨ p3578 ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4340) ∨ (¬ p4359))
    : (¬ p3146) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4340) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h29054 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55152 (p1992 p2027 p2245 p2545 p2608 p2641 p2963 p4111 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29056 : (¬ p1992) ∨ p2027 ∨ (¬ p2245) ∨ p2545 ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111))
    : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h29056 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55153 (p2027 p2470 p2528 p2608 p3519 p3591 p3923 p4348 p4376 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h29057 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p4503))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29057 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55155 (p1976 p2027 p2138 p2545 p2743 p2810 p2839 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29059 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ p2545 ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839))
    : (¬ p2138) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h29059 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55160 (p2027 p3146 p3641 p4158 p5107 p5160 p5175 : Prop)
    (h40810 : (¬ p2027))
    (h29064 : p2027 ∨ (¬ p3146) ∨ (¬ p3641) ∨ (¬ p4158) ∨ (¬ p5107) ∨ (¬ p5160) ∨ (¬ p5175))
    : (¬ p3146) ∨ (¬ p3641) ∨ (¬ p4158) ∨ (¬ p5107) ∨ (¬ p5160) ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29064 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55162 (p1988 p2027 p2388 p2761 p2901 p3212 p3556 p4135 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h29066 : (¬ p1988) ∨ p2027 ∨ p2388 ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135))
    : (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h29066 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55163 (p2027 p2668 p3550 p3568 p4260 p5559 : Prop)
    (h40810 : (¬ p2027))
    (h29068 : p2027 ∨ (¬ p2668) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p5559))
    : (¬ p2668) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29068 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55165 (p2027 p2331 p2753 p3347 p3540 p3644 p3755 p4117 p4195 p4330 p4348 p4367 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29070 : p2027 ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4367) ∨ (¬ p5216))
    : (¬ p2331) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4367) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h29070 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step55166 (p1986 p2027 p2373 p2997 p3054 p3097 p3694 p4110 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h29071 : (¬ p1986) ∨ p2027 ∨ (¬ p2373) ∨ p2997 ∨ (¬ p3054) ∨ (¬ p3097) ∨ (¬ p3694) ∨ (¬ p4110))
    : (¬ p2373) ∨ (¬ p3054) ∨ (¬ p3097) ∨ (¬ p3694) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h29071 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55167 (p2027 p2417 p2598 p2743 p2922 p3172 p3361 p3590 p3950 p4118 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h29072 : p2027 ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3590) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737))
    : (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3590) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29072 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55168 (p2027 p2406 p2499 p3016 p3742 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h29073 : p2027 ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4644))
    : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29073 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55170 (p2027 p2532 p2534 p3115 p3497 p4158 : Prop)
    (h40810 : (¬ p2027))
    (h29075 : p2027 ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4158))
    : (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29075 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55174 (p2027 p2254 p2363 p2518 p2928 p2963 p3389 p4079 p4118 p4196 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h29079 : p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p2963) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596))
    : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p2963) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29079 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55175 (p2027 p2657 p2946 p3412 p3684 p4210 p4750 : Prop)
    (h40810 : (¬ p2027))
    (h29080 : p2027 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p4750))
    : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29080 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55177 (p2027 p2252 p2750 p2819 p2952 p3093 p3570 p3954 p4024 p4133 p4320 : Prop)
    (h40810 : (¬ p2027))
    (h29082 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p4320))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29082 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55180 (p1997 p2027 p2114 p2737 p2811 p2901 p2946 p4235 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h29086 : (¬ p1997) ∨ p2027 ∨ p2114 ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235))
    : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h29086 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55182 (p1997 p2027 p2406 p2545 p2657 p2807 p2928 p3579 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29088 : (¬ p1997) ∨ p2027 ∨ (¬ p2406) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3579))
    : (¬ p2406) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h29088 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55184 (p2027 p2313 p2553 p2787 p2946 p3005 p3956 p4117 p4315 p4771 : Prop)
    (h40810 : (¬ p2027))
    (h29090 : p2027 ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4771))
    : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29090 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55191 (p2027 p2534 p3323 p3324 p4345 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h29098 : p2027 ∨ (¬ p2534) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4596))
    : (¬ p2534) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29098 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55192 (p2027 p2248 p2807 p3452 p3475 p3572 p3590 : Prop)
    (h40810 : (¬ p2027))
    (h29099 : p2027 ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p3590))
    : (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29099 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55195 (p2023 p2027 p2388 p3005 p3171 p3998 p4315 p5693 : Prop)
    (h2183 : p2023)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h29102 : (¬ p2023) ∨ p2027 ∨ p2388 ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4315) ∨ (¬ p5693))
    : (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4315) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2023 := h2183;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h29102 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55196 (p1990 p2027 p2545 p2563 p2685 p2810 p4066 p4235 p4283 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29103 : (¬ p1990) ∨ p2027 ∨ p2545 ∨ (¬ p2563) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283))
    : (¬ p2563) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2545) := h40876;
    (Or.elim h29103 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55197 (p2027 p2532 p2534 p3212 p4120 p4158 : Prop)
    (h40810 : (¬ p2027))
    (h29104 : p2027 ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4158))
    : (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29104 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55199 (p2027 p2241 p2352 p2598 p2750 p2753 p3032 p3422 p3553 p4133 p4366 : Prop)
    (h40810 : (¬ p2027))
    (h29107 : p2027 ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4366))
    : (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29107 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55201 (p1977 p2027 p2437 p2764 p2928 p3359 p3402 p4425 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h29109 : (¬ p1977) ∨ p2027 ∨ (¬ p2437) ∨ p2764 ∨ (¬ p2928) ∨ (¬ p3359) ∨ (¬ p3402) ∨ (¬ p4425))
    : (¬ p2437) ∨ (¬ p2928) ∨ (¬ p3359) ∨ (¬ p3402) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h29109 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55202 (p2027 p2252 p2750 p2952 p3440 p3497 p3692 p3830 p3954 p4181 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h29110 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3440) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5122))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3440) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29110 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55205 (p1992 p2027 p2633 p2657 p2743 p3361 p3644 p3742 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h29113 : (¬ p1992) ∨ p2027 ∨ p2633 ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3644) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h29113 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55215 (p1981 p2027 p2352 p2765 p3115 p3952 p4137 p5045 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h29124 : (¬ p1981) ∨ p2027 ∨ (¬ p2352) ∨ p2765 ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4137) ∨ (¬ p5045))
    : (¬ p2352) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4137) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h29124 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55218 (p2027 p2156 p2951 p3027 p3368 p3413 p4173 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h29127 : p2027 ∨ (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3027) ∨ (¬ p3368) ∨ (¬ p3413) ∨ (¬ p4173) ∨ (¬ p4652))
    : (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3027) ∨ (¬ p3368) ∨ (¬ p3413) ∨ (¬ p4173) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h29127 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step55220 (p1999 p2027 p2545 p2810 p3506 p3755 p4191 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29130 : (¬ p1999) ∨ p2027 ∨ p2545 ∨ (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191))
    : (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1999 := h2159;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h29130 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55224 (p2027 p2166 p2210 p3055 p3146 p3874 p4286 p4736 p5118 : Prop)
    (h40810 : (¬ p2027))
    (h29134 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4736) ∨ (¬ p5118))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4736) ∨ (¬ p5118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29134 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55228 (p2027 p2098 p2743 p2952 p3361 p3497 p3609 p4348 p4737 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h29139 : p2027 ∨ (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4737) ∨ (¬ p4905))
    : (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4737) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29139 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55230 (p2027 p2166 p2210 p3055 p3969 p4425 p4736 p5119 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h29142 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29142 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55231 (p2027 p2331 p3055 p3323 p3461 p3876 p4786 p4831 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h29143 : p2027 ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503))
    : (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29143 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55233 (p2027 p2533 p3680 p4134 p4347 p4444 : Prop)
    (h40810 : (¬ p2027))
    (h29145 : p2027 ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2533 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29145 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55235 (p2027 p2246 p2589 p2744 p2850 p3286 p3366 p3506 p3905 p4444 p4697 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h29147 : p2027 ∨ (¬ p2246) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3905) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5160))
    : (¬ p2246) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3905) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29147 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55236 (p2027 p3016 p3359 p3483 p4022 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h29148 : p2027 ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p5225))
    : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29148 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55246 (p1982 p2027 p2911 p2914 p3073 p3941 p5693 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h29159 : (¬ p1982) ∨ p2027 ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3073) ∨ (¬ p3941) ∨ (¬ p5693))
    : (¬ p2911) ∨ (¬ p3073) ∨ (¬ p3941) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h29159 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55248 (p2027 p2139 p2220 p2982 p3365 p3572 p3880 p3947 p4395 : Prop)
    (h40810 : (¬ p2027))
    (h29162 : p2027 ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3880) ∨ (¬ p3947) ∨ (¬ p4395))
    : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3880) ∨ (¬ p3947) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29162 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55249 (p2027 p2427 p2717 p3880 p3960 p4115 p4898 : Prop)
    (h40810 : (¬ p2027))
    (h29164 : p2027 ∨ (¬ p2427) ∨ (¬ p2717) ∨ (¬ p3880) ∨ (¬ p3960) ∨ (¬ p4115) ∨ (¬ p4898))
    : (¬ p2427) ∨ (¬ p2717) ∨ (¬ p3880) ∨ (¬ p3960) ∨ (¬ p4115) ∨ (¬ p4898) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29164 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55252 (p1991 p2027 p2633 p3414 p3644 p3868 p4391 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h29167 : (¬ p1991) ∨ p2027 ∨ p2633 ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4391))
    : (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4391) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3414 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h29167 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55257 (p2027 p2946 p3055 p3156 p3969 p4425 p4786 p5119 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h29173 : p2027 ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29173 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55260 (p2027 p2122 p2588 p3574 p4375 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h29176 : p2027 ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753))
    : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29176 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55261 (p2027 p2253 p2299 p2780 p2946 p3189 p3662 p3822 p4311 p4736 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h29177 : p2027 ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3822) ∨ (¬ p4311) ∨ (¬ p4736) ∨ (¬ p4902))
    : (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3822) ∨ (¬ p4311) ∨ (¬ p4736) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29177 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55262 (p2027 p2230 p2247 p2982 p2996 p3680 p4391 p4831 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h29178 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29178 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55263 (p2027 p2230 p2247 p2373 p3146 p4037 p4154 p4604 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h29179 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29179 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55269 (p1997 p2027 p2542 p3105 p3232 p3359 p3578 p3694 p4388 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h29186 : (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3105) ∨ (¬ p3232) ∨ (¬ p3359) ∨ p3578 ∨ (¬ p3694) ∨ (¬ p4388))
    : (¬ p2542) ∨ (¬ p3105) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3694) ∨ (¬ p4388) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3578) := h40900;
    (Or.elim h29186 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55272 (p2027 p2387 p3552 p3767 p4036 p4429 p4501 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h29189 : p2027 ∨ (¬ p2387) ∨ (¬ p3552) ∨ (¬ p3767) ∨ (¬ p4036) ∨ (¬ p4429) ∨ (¬ p4501) ∨ (¬ p5284))
    : (¬ p2387) ∨ (¬ p3552) ∨ (¬ p3767) ∨ (¬ p4036) ∨ (¬ p4429) ∨ (¬ p4501) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h29189 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step55273 (p1997 p2027 p2169 p2497 p2542 p2573 p3519 p3574 p3923 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h29190 : (¬ p1997) ∨ p2027 ∨ p2169 ∨ (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p3923))
    : (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2497 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2169) := h40866;
    (Or.elim h29190 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55275 (p1975 p2027 p2373 p2765 p3309 p3923 p4110 p4441 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h29192 : (¬ p1975) ∨ p2027 ∨ (¬ p2373) ∨ p2765 ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4110) ∨ (¬ p4441))
    : (¬ p2373) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4110) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h29192 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55276 (p2027 p2319 p2781 p2952 p3136 p3461 p3516 p4035 p4236 p4396 p4444 p5113 : Prop)
    (h40810 : (¬ p2027))
    (h29193 : p2027 ∨ (¬ p2319) ∨ (¬ p2781) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3461) ∨ (¬ p3516) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p5113))
    : (¬ p2319) ∨ (¬ p2781) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3461) ∨ (¬ p3516) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p5113) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29193 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55280 (p1990 p2027 p2166 p2241 p2284 p2699 p3497 p4365 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h29197 : (¬ p1990) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2241) ∨ (¬ p2284) ∨ p2699 ∨ (¬ p3497) ∨ (¬ p4365))
    : (¬ p2166) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h29197 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55281 (p2027 p2098 p2313 p2553 p2577 p3347 p3365 p3609 p4030 p4137 p4604 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h29198 : p2027 ∨ (¬ p2098) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4752))
    : (¬ p2098) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29198 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55285 (p2027 p2598 p2748 p3365 p3683 p4154 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h29204 : p2027 ∨ (¬ p2598) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4154) ∨ (¬ p4972))
    : (¬ p2598) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4154) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29204 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55288 (p2027 p2406 p2499 p2589 p3389 p4711 : Prop)
    (h40810 : (¬ p2027))
    (h29208 : p2027 ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4711))
    : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29208 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55289 (p2027 p2589 p2608 p3537 p4019 p4322 p4948 p5119 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h29210 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4019) ∨ (¬ p4322) ∨ (¬ p4948) ∨ (¬ p5119) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4019) ∨ (¬ p4322) ∨ (¬ p4948) ∨ (¬ p5119) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29210 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55290 (p1979 p2027 p2274 p2313 p2765 p3136 p3177 p3877 p4114 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h29211 : (¬ p1979) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2765 ∨ (¬ p3136) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4114))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3136) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4114) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1979 := h2139;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2765) := h40883;
    (Or.elim h29211 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step55293 (p1988 p2027 p2409 p2761 p2922 p3355 p3540 p4451 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h29215 : (¬ p1988) ∨ p2027 ∨ p2409 ∨ (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451))
    : (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2409) := h40874;
    (Or.elim h29215 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55294 (p2027 p2498 p2753 p3166 p3256 p3379 p3591 p3956 p4117 p4348 p4503 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29217 : p2027 ∨ (¬ p2498) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5216))
    : (¬ p2498) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29217 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55295 (p2027 p2145 p2563 p2807 p3005 p3572 p3646 p3880 p4117 p5063 : Prop)
    (h40810 : (¬ p2027))
    (h29218 : p2027 ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p5063))
    : (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29218 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55296 (p2027 p2098 p2579 p2588 p2753 p3347 p3609 p3692 p3945 p4107 p4902 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29219 : p2027 ∨ (¬ p2098) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4902) ∨ (¬ p5216))
    : (¬ p2098) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4902) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29219 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55297 (p2027 p2579 p2588 p2753 p2946 p3005 p3347 p3945 p4107 p4117 p4311 p4315 p4902 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29220 : p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p4902) ∨ (¬ p5216))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p4902) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h29220 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step55300 (p2027 p2373 p2406 p2928 p4001 p4904 : Prop)
    (h40810 : (¬ p2027))
    (h29225 : p2027 ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4904))
    : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29225 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55303 (p2027 p2449 p2685 p2696 p3486 p3555 p3570 p4668 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h29229 : p2027 ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p4733))
    : (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29229 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55320 (p2027 p2363 p2753 p2774 p2819 p3379 p3555 p4363 p5059 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h29251 : p2027 ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) ∨ (¬ p5216))
    : (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29251 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step55321 (p1994 p2027 p2630 p3623 p3830 p3853 p4035 p4366 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40903 : (¬ p3623))
    (h29252 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p3623 ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) ∨ (¬ p4366))
    : (¬ p2630) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3623) := h40903;
    (Or.elim h29252 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55322 (p2027 p2352 p3660 p3758 p3989 p4882 : Prop)
    (h40810 : (¬ p2027))
    (h29253 : p2027 ∨ (¬ p2352) ∨ (¬ p3660) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4882))
    : (¬ p2352) ∨ (¬ p3660) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29253 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55325 (p1976 p2027 p2138 p2545 p2839 p3016 p3688 p4342 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h29256 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ p2545 ∨ (¬ p2839) ∨ (¬ p3016) ∨ (¬ p3688) ∨ (¬ p4342))
    : (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3016) ∨ (¬ p3688) ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h29256 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55328 (p2010 p2027 p2707 p2842 p3434 p3585 p4278 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h29259 : (¬ p2010) ∨ p2027 ∨ (¬ p2707) ∨ p2842 ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p4278))
    : (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h29259 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55329 (p2027 p2132 p2657 p3105 p3680 p4256 p4286 p4789 p5123 : Prop)
    (h40810 : (¬ p2027))
    (h29260 : p2027 ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4789) ∨ (¬ p5123))
    : (¬ p2132) ∨ (¬ p2657) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4789) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29260 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55330 (p1975 p2027 p2299 p2765 p2870 p2881 p3758 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h29261 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2765 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758))
    : (¬ p2299) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h29261 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step55332 (p2027 p2954 p3005 p4120 p4311 p4315 : Prop)
    (h40810 : (¬ p2027))
    (h29263 : p2027 ∨ (¬ p2954) ∨ (¬ p3005) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4315))
    : (¬ p2954) ∨ (¬ p3005) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h29263 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step55334 (p2027 p2252 p2657 p2750 p3212 p3370 p3371 p3680 p3742 p4191 p4278 p4621 : Prop)
    (h40810 : (¬ p2027))
    (h29265 : p2027 ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621))
    : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29265 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55335 (p2027 p2156 p2252 p2750 p3105 p3370 p3371 p3414 p3553 p3758 p4348 p4450 : Prop)
    (h40810 : (¬ p2027))
    (h29266 : p2027 ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3758) ∨ (¬ p4348) ∨ (¬ p4450))
    : (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3758) ∨ (¬ p4348) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29266 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55336 (p1977 p2027 p2810 p2811 p3008 p3166 p3574 p4360 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h29267 : (¬ p1977) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p2811) ∨ p3008 ∨ (¬ p3166) ∨ (¬ p3574) ∨ (¬ p4360))
    : (¬ p2810) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3574) ∨ (¬ p4360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h29267 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55338 (p2027 p2144 p2252 p2363 p2619 p2750 p2753 p3051 p3172 p4118 p4244 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h29269 : p2027 ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4244) ∨ (¬ p4433))
    : (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4244) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29269 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55339 (p2027 p2132 p2534 p2657 p2870 p3246 p3950 p4256 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h29270 : p2027 ∨ (¬ p2132) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p4789))
    : (¬ p2132) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h29270 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step55342 (p2027 p2230 p2252 p2741 p2753 p2963 p2982 p3324 p3680 p4419 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h29273 : p2027 ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h29273 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step55344 (p1982 p2027 p2528 p2611 p3362 p3389 p3641 p3876 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h29275 : (¬ p1982) ∨ p2027 ∨ (¬ p2528) ∨ p2611 ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876))
    : (¬ p2528) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h29275 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step55346 (p2027 p2249 p2341 p2459 p2952 p3027 p3744 p4066 p4173 p4282 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h29277 : p2027 ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4066) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4604))
    : (¬ p2249) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4066) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2249 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h29277 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step55348 (p2027 p2088 p2166 p2534 p3696 p4607 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h29279 : p2027 ∨ (¬ p2088) ∨ (¬ p2166) ∨ (¬ p2534) ∨ (¬ p3696) ∨ (¬ p4607) ∨ (¬ p4632))
    : (¬ p2088) ∨ (¬ p2166) ∨ (¬ p2534) ∨ (¬ p3696) ∨ (¬ p4607) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h29279 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step55349 (p2027 p2245 p2641 p2717 p2963 p2996 p3471 p3570 p4362 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h29281 : p2027 ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p2996) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p2996) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h29281 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

end ElevenRUP
